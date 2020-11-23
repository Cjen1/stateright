//! Private module for selective re-export.

use crate::{CheckerBuilder, CheckerVisitor, Fingerprint, fingerprint, Model, Property};
use crate::checker::{Checker, Expectation, Path};
use dashmap::DashMap;
use dashmap::mapref::entry::Entry;
use nohash_hasher::NoHashHasher;
use parking_lot::{Condvar, Mutex};
use std::collections::{HashMap, VecDeque};
use std::hash::{BuildHasherDefault, Hash};
use std::sync::Arc;

pub(crate) struct BfsChecker<M: Model> {
    model: Arc<M>,
    thread_count: usize,
    handles: Vec<std::thread::JoinHandle<()>>,
    job_market: Arc<Mutex<JobMarket<M::State>>>,
    generated: Arc<DashMap<Fingerprint, Option<Fingerprint>, BuildHasherDefault<NoHashHasher<u64>>>>,
    discoveries: Arc<DashMap<&'static str, Fingerprint>>,
}
struct JobMarket<State> { wait_count: usize, jobs: Vec<Job<State>> }
type Job<State> = VecDeque<(State, Fingerprint)>;

impl<M> BfsChecker<M>
where M: Model + Send + Sync + 'static,
      M::State: Hash + Send + 'static,
{
    pub(crate) fn spawn(options: CheckerBuilder<M>) -> Self {
        let model = Arc::new(options.model);
        let target_generated_count = options.target_generated_count;
        let thread_count = options.thread_count;
        let visitor = Arc::new(options.visitor);
        let property_count = model.properties().len();

        let generated = Arc::new(DashMap::default());
        for s in model.init_states() { generated.insert(fingerprint(&s), None); }
        let pending: VecDeque<_> = model.init_states().into_iter()
            .map(|s| {
                let fp = fingerprint(&s);
                (s, fp)
            })
            .collect();
        let discoveries = Arc::new(DashMap::default());
        let mut handles = Vec::new();

        let has_new_job = Arc::new(Condvar::new());
        let job_market = Arc::new(Mutex::new(JobMarket {
            wait_count: thread_count,
            jobs: vec![pending],
        }));
        for t in 0..thread_count {
            let model = Arc::clone(&model);
            let visitor = Arc::clone(&visitor);
            let has_new_job = Arc::clone(&has_new_job);
            let job_market = Arc::clone(&job_market);
            let generated = Arc::clone(&generated);
            let discoveries = Arc::clone(&discoveries);
            handles.push(std::thread::spawn(move || {
                log::debug!("{}: Thread started.", t);
                let mut pending = VecDeque::new();
                loop {
                    // Step 1: Do work.
                    if pending.is_empty() {
                        pending = {
                            let mut job_market = job_market.lock();
                            match job_market.jobs.pop() {
                                None => {
                                    // Done if all are waiting.
                                    if job_market.wait_count == thread_count {
                                        log::debug!("{}: No more work. Shutting down... gen={}", t, generated.len());
                                        has_new_job.notify_all();
                                        return
                                    }

                                    // Otherwise more work may become available.
                                    log::trace!("{}: No jobs. Awaiting. blocked={}", t, job_market.wait_count);
                                    has_new_job.wait(&mut job_market);
                                    continue
                                }
                                Some(job) => {
                                    job_market.wait_count -= 1;
                                    log::trace!("{}: Job found. size={}, blocked={}", t, job.len(), job_market.wait_count);
                                    job
                                }
                            }
                        };
                    }
                    Self::check_block(&*model, &*generated, &mut pending, &*discoveries, &*visitor, 1500);
                    if discoveries.len() == property_count {
                        log::debug!("{}: Discovery complete. Shutting down... gen={}", t, generated.len());
                        let mut job_market = job_market.lock();
                        job_market.wait_count += 1;
                        drop(job_market);
                        has_new_job.notify_all();
                        return
                    }
                    if let Some(target_generated_count) = target_generated_count {
                        if target_generated_count.get() <= generated.len() {
                            log::debug!("{}: Reached target generated count. Shutting down... gen={}", t, generated.len());
                            return;
                        }
                    }

                    // Step 2: Share work.
                    if pending.len() > 1 && thread_count > 1 {
                        let mut job_market = job_market.lock();
                        let pieces = 1 + std::cmp::min(job_market.wait_count as usize, pending.len());
                        let size = pending.len() / pieces;
                        for _ in 1..pieces {
                            log::trace!("{}: Sharing work. blocked={}, size={}", t, job_market.wait_count, size);
                            job_market.jobs.push(pending.split_off(pending.len() - size));
                            has_new_job.notify_one();
                        }
                    } else if pending.is_empty() {
                        let mut job_market = job_market.lock();
                        job_market.wait_count += 1;
                    }
                }
            }));
        }
        BfsChecker {
            model,
            thread_count,
            handles,
            job_market,
            generated,
            discoveries,
        }
    }

    fn check_block(
        model: &M,
        generated: &DashMap<Fingerprint, Option<Fingerprint>, BuildHasherDefault<NoHashHasher<u64>>>,
        pending: &mut Job<M::State>,
        discoveries: &DashMap<&'static str, Fingerprint>,
        visitor: &Option<Box<dyn CheckerVisitor<M> + Send + Sync>>,
        mut max_count: usize)
    {
        let properties = model.properties();

        let mut actions = Vec::new();
        loop {
            // Done if reached max count.
            if max_count == 0 { return }
            max_count -= 1;

            // Done if none pending.
            let (state, state_fp) = match pending.pop_back() {
                None => return,
                Some(pair) => pair,
            };
            if let Some(visitor) = visitor {
                visitor.visit(reconstruct_path(model, generated, state_fp));
            }

            // Done if discoveries found for all properties.
            let mut is_awaiting_discoveries = false;
            for property in &properties {
                if discoveries.contains_key(property.name) { continue }
                match property {
                    Property { expectation: Expectation::Always, condition: always, .. } => {
                        if !always(model, &state) {
                            // Races other threads, but that's fine.
                            discoveries.insert(property.name, state_fp);
                        } else {
                            is_awaiting_discoveries = true;
                        }
                    },
                    Property { expectation: Expectation::Sometimes, condition: sometimes, .. } => {
                        if sometimes(model, &state) {
                            // Races other threads, but that's fine.
                            discoveries.insert(property.name, state_fp);
                        } else {
                            is_awaiting_discoveries = true;
                        }
                    },
                    Property { expectation: Expectation::Eventually, condition: _eventually, .. } => {
                        // FIXME: port over Graydon's implementation
                    }
                }

            }
            if !is_awaiting_discoveries { return }

            // Otherwise enqueue newly generated states and fingerprint traces.
            model.actions(&state, &mut actions);
            let next_states = actions.drain(..).flat_map(|a| model.next_state(&state, a));
            for next_state in next_states {
                // Skip if outside boundary.
                if !model.within_boundary(&next_state) { continue }

                // Skip if already generated.
                let next_fingerprint = fingerprint(&next_state);
                if let Entry::Vacant(next_entry) = generated.entry(next_fingerprint) {
                    next_entry.insert(Some(state_fp));
                } else { continue }

                // Otherwise checking is applicable.
                pending.push_front((next_state, next_fingerprint));
            }
        }
    }
}

impl<M> Checker<M> for BfsChecker<M>
where M: Model,
      M::State: Hash,
{
    fn model(&self) -> &M { &self.model }

    fn generated_count(&self) -> usize { self.generated.len() }

    fn discoveries(&self) -> HashMap<&'static str, Path<M::State, M::Action>> {
        self.discoveries.iter()
            .map(|mapref| {
                (
                    <&'static str>::clone(mapref.key()),
                    reconstruct_path(self.model(), &*self.generated, *mapref.value()),
                )
            })
            .collect()
    }

    fn join(mut self) -> Self {
        for h in self.handles.drain(0..) {
            h.join().unwrap();
        }
        self
    }

    fn is_done(&self) -> bool {
        let job_market = self.job_market.lock();
        job_market.jobs.is_empty() && job_market.wait_count == self.thread_count
            || self.discoveries.len() == self.model.properties().len()
    }
}

fn reconstruct_path<M>(
    model: &M,
    generated: &DashMap<Fingerprint, Option<Fingerprint>, BuildHasherDefault<NoHashHasher<u64>>>,
    fp: Fingerprint)
    -> Path<M::State, M::Action>
    where M: Model,
          M::State: Hash,
{
    // First build a stack of digests representing the path (with the init digest at top of
    // stack). Then unwind the stack of digests into a vector of states. The TLC model checker
    // uses a similar technique, which is documented in the paper "Model Checking TLA+
    // Specifications" by Yu, Manolios, and Lamport.

    let mut fingerprints = VecDeque::new();
    let mut next_fp = fp;
    while let Some(source) = generated.get(&next_fp) {
        match *source {
            Some(prev_fingerprint) => {
                fingerprints.push_front(next_fp);
                next_fp = prev_fingerprint;
            },
            None => {
                fingerprints.push_front(next_fp);
                break;
            },
        }
    }
    Path::from_fingerprints(model, fingerprints)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::*;
    use crate::test_util::linear_equation_solver::*;

    #[test]
    fn visits_states_in_bfs_order() {
        let (recorder, accessor) = StateRecorder::new_with_accessor();
        LinearEquation { a: 2, b: 10, c: 14 }.checker()
            .visitor(recorder)
            .spawn_bfs().join();
        assert_eq!(
            accessor(),
            vec![
                (0, 0),                 // distance == 0
                (1, 0), (0, 1),         // distance == 1
                (2, 0), (1, 1), (0, 2), // distance == 2
                (3, 0), (2, 1),         // distance == 3
            ]);
    }

    #[test]
    fn can_complete_by_enumerating_all_states() {
        let checker = LinearEquation { a: 2, b: 4, c: 7 }.checker().spawn_bfs().join();
        assert_eq!(checker.is_done(), true);
        checker.assert_no_discovery("solvable");
        assert_eq!(checker.generated_count(), 256 * 256);
    }

    #[test]
    fn can_complete_by_eliminating_properties() {
        let checker = LinearEquation { a: 2, b: 10, c: 14 }.checker().spawn_bfs().join();
        checker.assert_properties();
        assert_eq!(checker.generated_count(), 12);

        // bfs found this example...
        assert_eq!(
            checker.discovery("solvable").unwrap().into_actions(),
            // (2*2 + 10*1) % 256 == 14
            vec![
                Guess::IncreaseX,
                Guess::IncreaseX,
                Guess::IncreaseY,
            ]);
        // ... but there are of course other solutions, such as the following.
        checker.assert_discovery(
            "solvable",
            // (2*0 + 10*27) % 256 == 14
            vec![Guess::IncreaseY; 27]);
    }
}
