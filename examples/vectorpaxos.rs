use serde::{Deserialize, Serialize};
use stateright::{Model, Rewrite, RewritePlan, Checker, Expectation};
use stateright::actor::{Actor, Out, Id, ActorModelState, majority, ActorModel, Envelope, DuplicatingNetwork, FiniteNetwork};
use stateright::actor::write_once_register::{WORegisterActor, WORegisterActorState, WORegisterMsg, WORegisterMsg::*};
use stateright::semantics::write_once_register::WORegister;
use stateright::semantics::LinearizabilityTester;
use stateright::util::{HashableHashMap, HashableHashSet};
use std::borrow::Cow;
use std::sync::Arc;
use std::time::Duration;
use std::ops::Range;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashSet, HashMap};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

// This module is a feasibility prototype for an exhaustively checked variant of Paxos
//
// Checking 2 clients (and hence 2 values), 2 proposers, 1 acceptor and at most one message per
// channel, it completed in 22 hrs with 9M states after exploring 51M
//
// $> cargo run --example vectorpaxos check-full 2 2 1 1
// ...
// Done. states=51,618,942, unique=9,811,774, sec=77111
//
// TLA+ spec:
// 
// ProposerState:
//   id \in ProposerIds
//   bal \in BallotNumbers<Mutable>
//   rid \in RoundIds * ProposerIds \\ infinite scalarset
//   sm \in [kind : Candidate, votes : SUBSET AcceptorIds]
//     \cup [kind : Leader, votes : SUBSET AcceptorIds, value : Value]
//
// AcceptorState:
//   id \in AcceptorIds
//   maxBal \in BallotNumbers<Immutable>
//   crid \in RoundIds, \cup None
//   maxVBal \in BallotNumbers<Immutable>
//   maxVVal \in Values \cup None
//
// init:
//   \A p in Proposers:
//     p = [bal : BalNum(p.id, {}), 
//          rid = (RoundId.new(), p.id),
//          sm : [kind : Candidate, votes : {}]]
//   \A a in Acceptors:
//     a = [maxBal : BalNum(a.id, {}),
//          crid : (RoundId.new(), a.id),
//          maxVBal : BalNum(a.id, {}),
//          maxVVal : None]
//
// timeout for Proposer p:
//   if p.sm.kind = Candidate 
//     if |p.sm.votes| < quorum-1(|acceptor_ids|):
//       max_val = \\ value of ballot with largest number or arbitrary if none
//       p.sm <- [kind : Leader, votes : {}, value : max_val]
//       p.rid <- (rid \in RoundIds, p.id)
//     else
//       broadcast([kind : 1a, bal : p.bal.get(), rid : p.rid])
//   else if p.sm.kind = Leader 
//     if |p.sm.votes| < quorum-2(|acceptor_ids|):
//       broadcast([kind: 2a, bal : p.bal.bet(), val : p.sm.val, rid : p.rid])
//     else:
//       commit(p.sm.value)
//
// on recv [kind: nack, bal] to p \in Proposers:
//   p.bal.mint(bal)
//   p.rid = (p.id, RoundId.new());
//   p.sm = [kind : Candidate, votes : {}]
//     
// on recv [kind : 1a, bal, rid] to a \in Acceptors from p \in Proposers:
//   if a.bal < bal:
//     p.maxBal = bal
//     send(p, [kind : 1b, bal : bal, rid])
//   else:
//     send(p, [kind: nack, bal: a.maxBal])
//
// on recv [kind: 1b, bal, rid] to p \in Proposers from a:
//   if rid = p.rid and p.sm.kind = Candidate:
//     p.sm.votes = p.sm.votes \cup {a}
//
// on recv [kind: 2a, bal, val, rid] to a \in Acceptors from p \in Proposers:
//   if rid = a.crid or a.bal < bal:
//     a.crid = rid
//     a.maxBal = bal
//     a.maxVBal = bal
//     a.maxVVal = val
//     send(p, [kind: 2b, rid: rid])
//   else:
//     send(p, [kind: nack, p.maxBal])
//
// on recv [kind: 2b, rid] to p \in Proposers from a \in Acceptors:
//   if rid = p.rid:
//     p.sm.votes = p.sm.votes \cup {a}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
#[derive(Serialize, Deserialize)]
struct Mutable;
#[derive(Hash, PartialEq, Eq, Clone, Debug)]
#[derive(Serialize, Deserialize)]
struct Immutable;
#[derive(Hash, PartialEq, Eq, Clone, Debug)]
#[derive(Serialize, Deserialize)]
// ModelBalNum reduces the cost of the equivalence reduction
enum BalNum {
    Impl(Id, HashableHashSet<Arc<BalNum>>),
    Modl(u64),
}

impl BalNum {
    fn unwrap(&self) -> (&Id, &HashableHashSet<Arc<BalNum>>){
        match self {
            BalNum::Impl(i,d) => (i,d),
            _ => unimplemented!()
        }
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
#[derive(Serialize, Deserialize)]
struct BallotNumber<K: Hash + Eq>(Arc<BalNum>, PhantomData<K>);

impl<K: Hash + Eq> BallotNumber<K> {
    fn new(id: Id) -> BallotNumber<Mutable> { 
        BallotNumber(Arc::new(BalNum::Impl(id, HashableHashSet::new())), PhantomData) }

    fn get(&self) -> BallotNumber<Immutable> {
        match self {
            BallotNumber(b, _) => BallotNumber(b.clone(), PhantomData),
        }
    }

    fn unwrap(&self) -> &Arc<BalNum> {
        match self {
            BallotNumber(b, _) => b,
        }

    }

    fn mint<Y: Hash + Eq>(
        &mut self,
        y : &BallotNumber<Y>) {
        let BallotNumber(a, _) = self;
        let BallotNumber(b, _) = y;
        let (i_a, d_a) = a.unwrap();
        let (_, d_b) = b.unwrap();
        let mut new_deps = HashableHashSet::new();
        for ba in d_a.iter() { new_deps.insert(ba.clone()); }
        for bb in d_b.iter() { new_deps.insert(bb.clone()); }
        new_deps.insert(a.clone());
        new_deps.insert(b.clone());
        *self = BallotNumber(Arc::new(BalNum::Impl(i_a.clone(), new_deps)), PhantomData)
    }

    fn depth(&self) -> usize {
        let BallotNumber(a, _) = self;
        match &**a {
            BalNum::Impl(_, d_a) => d_a.len(),
            _ => unimplemented!(),
        }
    }
}

impl<K: Hash + Eq> BallotNumber<K> {
    fn less_than<L: Hash + Eq>(&self, other : &BallotNumber<L>) -> bool {
        let BallotNumber(a, _) = self;
        let BallotNumber(b, _) = other;
        let (_, d_b) = b.unwrap();
        d_b.contains(a)
    }

    fn explicit_equals(&self, other : &BallotNumber<K>) -> bool {
        let BallotNumber(a, _) = self;
        let BallotNumber(b, _) = other;
        a == b
    }
}

#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn ballot_cmp() {
        let a0 = BallotNumber::<Mutable>::new(0.into());
        let a1 = BallotNumber::<Mutable>::new(1.into());

        assert_eq!(a0.less_than(&a1), false);

        let mut b0 = a0.clone();
        b0.mint(&a1.get());
        let mut b1 = a1.clone();
        b1.mint(&a0.get());

        let mut c = b0.clone();
        c.mint(&BallotNumber::<Mutable>::new(2.into()));

        let tests = vec![
            (vec![&a0], vec![&a1], false),
            (vec![&a0], vec![&a1], false),
            (vec![&b1], vec![&b0], false),
            (vec![&b1], vec![&b0], false),

            (vec![&a0, &a1], vec![&b0,&b1], true),
            (vec![&b0,&b1], vec![&a0,&a1], false),

            (vec![&c], vec![&b0, &a0, &a1], false),
            (vec![&b0, &a0, &a1], vec![&c],  true),
            (vec![&c], vec![&b1], false),
        ];

        for (src, dst, exp) in tests {
            for s in &src {
                for d in &dst {
                    println!("{:?}\n --- .less_than --- \n {:?}\n --- expecting {:?} ---\n ============", s, d, exp);
                    assert_eq!(s.less_than(&d), exp)
                }
            }
        }
    }

    #[test]
    fn ballot_depth() {
        let a0 = BallotNumber::<Mutable>::new(0.into());
        let a1 = BallotNumber::<Mutable>::new(1.into());

        let mut b0 = a0.clone();
        b0.mint(&a1);
        let mut b1 = a1.clone();
        b1.mint(&a0);

        let mut c = b0.clone();
        c.mint(&BallotNumber::<Mutable>::new(2.into()));
        
        assert_eq!(a0.depth(), 0);
        assert_eq!(a1.depth(), 0);

        assert_eq!(b0.depth(), 2);
        assert_eq!(b1.depth(), 2);

        assert_eq!(c.depth(), 4);
    }
}


type Value = char;
type RequestId = u64;

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
#[derive(Serialize, Deserialize)]
enum VPaxosMsg {
    MNack { ballot: BallotNumber<Immutable> },

    M1a   { ballot: BallotNumber<Immutable> },
    M1b   { ballot: BallotNumber<Immutable>, last_accepted: Option<(BallotNumber<Immutable>, Value)> },

    M2a   { ballot: BallotNumber<Immutable>, value: Value },
    M2b   { ballot: BallotNumber<Immutable> },
}
use VPaxosMsg::*;

#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
enum ProposerSM {
    Candidate{votes : HashableHashMap<Id, Option<(BallotNumber<Immutable>, Value)>>},
    Leader{value : Option<Value>, votes : HashableHashSet<Id>}, // Chosen value and vector of votes
}
use ProposerSM::*;

#[derive(Clone, Debug, Hash, PartialEq, PartialOrd, Eq, Ord)]
enum ClientMsg {
    Put(Id, u64, Value),
    Get(Id, u64),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum VPaxosActorState {
    Proposer {
        bal: BallotNumber<Mutable>,
        state: ProposerSM,
        pending_clients: Vec<ClientMsg>,
    },
    Acceptor{
        max_bal: BallotNumber<Immutable>,
        max_vbal: Option<(BallotNumber<Immutable>, Value)>,
    },
}
use VPaxosActorState::*;

#[derive(Clone, Debug)]
enum VPaxosKind {
    Proposer,
    Acceptor,
}

#[derive(Clone, Debug)]
struct VPaxosActor { 
    kind: VPaxosKind,
    // proposer_ids: Vec<Id>,
    acceptor_ids: Vec<Id> 
}

fn select_value(ballots: Vec<Option<(BallotNumber<Immutable>, Value)>>) -> Option<Value> {
    let mut max_bal = ballots[0].clone();
    for b in ballots.into_iter() {
        match(&b, &max_bal) {
            (_, None) => { max_bal = b; }
            (Some((tb, _)), Some((mb, _))) if mb.less_than(&tb) => { 
                max_bal = b;
            }
            _ => ()
        }
    }
    match max_bal {
        None => None,
        Some((_,v)) => Some(v)
    }
}


fn model_timeout() -> Range<Duration> {
    Duration::from_micros(0)..Duration::from_micros(0)
}
impl Actor for VPaxosActor {
    type Msg = WORegisterMsg<RequestId, Value, VPaxosMsg>;
    type State = VPaxosActorState;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        o.set_timer(model_timeout());
        match self.kind {
            VPaxosKind::Proposer => Proposer{bal : BallotNumber::<Mutable>::new(id), state : Candidate{votes: HashableHashMap::new()}, pending_clients : vec![]},
            VPaxosKind::Acceptor => Acceptor{max_bal : BallotNumber::<Mutable>::new(0.into()).get(), max_vbal : None},
        }
    }

    fn on_timeout(&self, _id: Id, state: &mut Cow<Self::State>, o: &mut Out<Self>)
    {
        // Refresh timer to fire on next iteration
        o.set_timer(model_timeout());

        // Not entirely happy with this, should be able to take any of these actions, rather than
        // deterministically choosing one...
        match &**state {
            // Become a leader
            // ~Phase2a(p) Value select
            Proposer{state : Candidate{votes}, bal:_, pending_clients} if votes.len() >= majority(self.acceptor_ids.len()) => {
                let values : Vec<Option<(BallotNumber<Immutable>,Value)>> = votes.iter()
                    .map(|(_, v)| v.clone())
                    .collect();
                // If no value has been proposed select any submitted one
                let new_value = select_value(values).or_else(|| 
                    pending_clients.iter()
                    .find_map(|x| match x {
                        ClientMsg::Put(_, _, v) => Some(*v),
                        ClientMsg::Get(_, _) => None,
                    })
                );
                match state.to_mut(){
                    Proposer {bal, state, pending_clients:_} => {
                        bal.mint(&bal.get());
                        *state = Leader{value: new_value, votes : HashableHashSet::new()};
                    },
                    _ => unreachable!(),
                };
            },
            // Transmit 1a messages
            Proposer{state : Candidate{ .. }, bal, ..} => {
                let msg = Internal(M1a{ballot : bal.get()});
                o.broadcast(&self.acceptor_ids, &msg);
            }
            // If a value is committed then reply to clients
            Proposer{state : Leader{value : Some(value), votes}, pending_clients, ..} if votes.len() >= majority(self.acceptor_ids.len()) => {
                for c in pending_clients {
                    let (cid, msg) = match c {
                        ClientMsg::Put(c, rid, v) if v == value => (*c, PutOk(*rid)),
                        ClientMsg::Put(c, rid, _)               => (*c, PutFail(*rid)),
                        ClientMsg::Get(c, rid)                  => (*c, GetOk(*rid, *value)),
                    };
                    o.send(cid, msg)
                }
            }
            // ~Phase2a(p) broadcast phase2a(bal, val)
            Proposer{bal, state : Leader{value : Some(value), ..}, ..} => {
                let msg = Internal(M2a{ballot : bal.get(), value: value.clone()});
                o.broadcast(&self.acceptor_ids, &msg);
            }
            _ => {}
        };
    }

    fn on_msg(&self, _id: Id, state: &mut Cow<Self::State>, src: Id, msg: Self::Msg, o: &mut Out<Self>)
    {
        match (&**state, &msg) {
            // ~Phase1b and ~Phase2b when the ballot is too small
            (Acceptor{max_bal, ..}, Internal(M1a{ballot : mbal})) 
                | (Acceptor{max_bal, ..}, Internal(M2a{ballot : mbal, ..}))
                if !(max_bal.less_than(mbal)) => {
                o.send(src, Internal(MNack{ballot : max_bal.clone()}));
            }
            // If a nack is received for a ballot which is not less than the current one
            (Proposer{bal, ..}, Internal( MNack{ballot : mbal} )) if !(mbal.less_than(&bal.get())) => {
                match state.to_mut() {
                    Proposer{bal, state, pending_clients:_} => {
                        bal.mint(mbal);
                        *state = Candidate{votes: HashableHashMap::new()};
                    }
                    _ => unreachable!()
                }
            }
            // ~Phase1b(a)
            (Acceptor{max_bal, max_vbal}, Internal(M1a{ballot : mbal})) if max_bal.less_than(mbal) => {
                o.send(src, Internal(M1b{ballot : mbal.clone(), last_accepted : max_vbal.clone()}));
                *state.to_mut() = Acceptor{max_bal : mbal.clone(), max_vbal : max_vbal.clone()};
            }
            // ~Phase1b.2(p) necessary since cannot just do \E M \subset msgs: quorum(1b, acceptors, M, ballot)
            (Proposer{bal, state : Candidate{votes}, ..}, Internal(M1b{ballot: mbal, last_accepted})) if bal.get().explicit_equals(&mbal.get()) => {
                let mut new_votes = votes.clone();
                new_votes.insert(src, last_accepted.clone());
                match state.to_mut() {
                    Proposer{state: Candidate{votes}, ..} => { *votes = new_votes; }
                    _ => unreachable!()
                }
            }
            // ~Phase2b(a)
            (Acceptor{max_bal, ..}, Internal(M2a{ballot: mbal, value})) if max_bal.less_than(&mbal) => {
                let msg = Internal(M2b{ballot : mbal.get()});
                o.send(src, msg);
                match state.to_mut() {
                    Acceptor{max_vbal, ..} => { *max_vbal = Some((mbal.get(), value.clone())); }
                    _ => unreachable!()
                }
            }
            // ~Phase3(p) receive phase2b message
            (Proposer{bal, state : Leader{votes, ..}, ..}, Internal(M2b{ballot : mbal})) if bal.get().explicit_equals(&mbal.get()) => {
                let mut new_votes = votes.clone();
                new_votes.insert(src); 
                match state.to_mut() {
                    Proposer{state: Leader{votes, ..}, .. } => {
                        *votes = new_votes;
                    }
                    _ => unreachable!()
                }
            }
            (Proposer{bal, ..}, Put(rid, put_value)) => {
                let mbal = bal.get();
                match state.to_mut() {
                    Proposer{pending_clients, state, ..} => {
                        match state {
                            Leader{value: value @ None, ..} => {
                                let msg = Internal(M2a{ballot : mbal, value: *put_value});
                                o.broadcast(&self.acceptor_ids, &msg);
                                *value = Some(*put_value);
                            }
                            _ => ()
                        };

                        let mut new_pending_clients = pending_clients.clone();
                        new_pending_clients.push(ClientMsg::Put(src, *rid, *put_value));
                        *pending_clients = new_pending_clients;
                    }
                    _ => unreachable!()
                }
            },
            (Proposer{pending_clients, ..}, Get(rid)) => {
                let mut new_pending_clients = pending_clients.clone();
                new_pending_clients.push(ClientMsg::Get(src, *rid));
                match state.to_mut() {
                    Proposer{pending_clients, ..} => { *pending_clients = new_pending_clients; }
                    _ => unreachable!()
                }
            },
            _ => {}
        }
    }
}


fn all_ballots<'a, H>(state : &'a ActorModelState<WORegisterActor<VPaxosActor>, H>) -> HashSet<Arc<BalNum>> {
    use WORegisterActorState::*;
    let mut active_ballots : HashSet<Arc<BalNum>> = HashSet::new();
    // Add all used ballots from nodes
    for node in &state.actor_states {
        match &**node {
            Server(Proposer{state : Candidate{votes}, bal, ..}) => { 
                active_ballots.insert(bal.unwrap().clone());
                for (_, vote) in votes.into_iter() {
                    match vote {
                        None => {}
                        Some((b,_)) => { active_ballots.insert(b.unwrap().clone()); }
                    };
                };
            }
            // Just follower and leader remain
            Server(Acceptor {max_bal: bal, max_vbal : None}) => { active_ballots.insert(bal.unwrap().clone()); }
            Server(Proposer {bal, .. }) => { active_ballots.insert(bal.unwrap().clone()); },
            Server(Acceptor {max_bal, max_vbal : Some((max_vbal, _))}) => { 
                active_ballots.insert(max_bal.unwrap().clone());
                active_ballots.insert(max_vbal.unwrap().clone());
            }
            _ => {}
        }
    };
    // Add all used ballots from messages
    for Envelope{msg, .. } in state.network.into_iter() {
        match msg {
            WORegisterMsg::Internal(MNack{ ballot, .. })
                | WORegisterMsg::Internal(M1a{ ballot, .. })
                | WORegisterMsg::Internal(M1b{ ballot, last_accepted : None })
                | WORegisterMsg::Internal(M2a{ ballot, .. })
                | WORegisterMsg::Internal(M2b{ ballot, .. })
                => { active_ballots.insert(ballot.unwrap().clone()); }
            WORegisterMsg::Internal(M1b{ ballot, last_accepted : Some((la_bal, _)) }) => { 
                active_ballots.insert(ballot.unwrap().clone());
                active_ballots.insert(la_bal.unwrap().clone());
            }
            _ => {}
        }
    };
    active_ballots
}

fn build_ballot_rewriter(ballots : HashSet<Arc<BalNum>>) 
    -> RewritePlan<BalNum, HashMap<BalNum, u64>> {
    // This algorithm relies on how we mint ballots
    // a < b => |a.deps| < |b.deps|
    // Proof:
    //     a < b => /\ a \in b.deps
    //              /\ a.deps \subset b.deps (by transitivity)
    //     a \notin a.deps
    //     Thus |b.deps| > |a.deps|
    //
    // We want to normalise ballots such that we have already visited all dependencies of a ballot
    // before we visit the ballot
    //
    // Thus we sort based on length of dependencies
    // If we take two ballots wlg assume we visit a before b
    //   => |a.deps| <= |b.deps|
    //   => ~ |b.deps| < |a.deps|
    //   => ~ b < a
    //
    // Thus a cannot depend on b
    // Thus if b depends on a, then a will be visited before b
    
    let mut mapping : HashMap<BalNum, u64> = HashMap::new();
    let mut sorted_bals = ballots.iter().collect::<Vec<_>>();
    sorted_bals.sort_by_cached_key(|&b| {
        let (_,d) = b.unwrap();
        d.len()
    });
    for &ballot in sorted_bals.iter() {
        let (i,d) = ballot.unwrap();
        let mut hasher = DefaultHasher::new();
        i.hash(&mut hasher);
        for dep_bal in d {
            match mapping.get(dep_bal) {
                None => (), // Thus it is not an active ballot
                Some(h) => h.hash(&mut hasher)
            }
        }
        mapping.insert((**ballot).clone(), hasher.finish());
    }

    RewritePlan::new(
        mapping,
        |b, s| {
            let hash = s.get(b).unwrap();
            BalNum::Modl(*hash)
        }
    )
}

fn symmetry_fn<H: Clone + 'static>(state : &ActorModelState<WORegisterActor<VPaxosActor>,H>) -> ActorModelState<WORegisterActor<VPaxosActor>,H> 
{
    let ballot_rewrite_plan = build_ballot_rewriter(all_ballots(state));
    ActorModelState {
        actor_states : state.actor_states.rewrite(&ballot_rewrite_plan),
        network : state.network.rewrite(&ballot_rewrite_plan),
        .. (state.clone())
    }
}

#[derive(Clone, Debug)]
struct VPaxosModelCfg {
    client_count:   usize,
    proposer_count: usize,
    acceptor_count: usize,
    //channel_length: usize,
}

fn exclude(i : Id, ids : &Vec<Id>) -> Vec<Id> {
    ids.iter()
        .filter(|&x| *x != i)
        .map(|&x| x.into())
        .collect()
}

impl VPaxosModelCfg {
    fn into_model(self) ->
        ActorModel<
            WORegisterActor<VPaxosActor>,
            Self,
            LinearizabilityTester<Id,WORegister<Value>>>
    {
        //let proposer_ids : Vec<Id> = (0..self.proposer_count)
        //    .map(|x| x.into())
        //    .collect();
        let acceptor_ids : Vec<Id> = (self.proposer_count..(self.proposer_count + self.acceptor_count))
            .map(|x| x.into())
            .collect();
        ActorModel::new(
            self.clone(),
            LinearizabilityTester::new(WORegister(None)))
        // proposer ids \in [0,proposer_count)
        .actors((0..self.proposer_count)
            .map(|_| WORegisterActor::Server(VPaxosActor {
                kind: VPaxosKind::Proposer,
                //proposer_ids : exclude(i.into(), &proposer_ids),
                acceptor_ids : acceptor_ids.clone(),
            }))
        )
        // acceptor ids \in [proposer_count,proposer_count + acceptor_count)
        .actors((0..self.acceptor_count)
            .map(|i| WORegisterActor::Server(VPaxosActor {
                kind: VPaxosKind::Acceptor,
                //proposer_ids : proposer_ids.clone(),
                acceptor_ids : exclude((i + self.proposer_count).into(), &acceptor_ids),
            }))
        )
        // clients
        .actors((0..self.client_count)
            .map(|_| WORegisterActor::Client {
                put_count: 1,
                server_count: self.proposer_count
            })
        )
        .duplicating_network(DuplicatingNetwork::No)
        .property(Expectation::Sometimes, "value chosen", |_, state| {
            for env in &state.network {
                if let WORegisterMsg::GetOk(_req_id, _value) = env.msg {
                    return true
                }
            }
            false
        })
        //.property(Expectation::Sometimes, "1 received vote", |_, state| {
        //    for env in &state.network {
        //        if let WORegisterMsg::Internal(VPaxosMsg::MNack{..}) = env.msg {
        //            if env.dst == 1.into() {
        //                return true
        //            }
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "1. value sent", |_, state| {
        //    for env in &state.network {
        //        if let WORegisterMsg::Put(_,_) = env.msg {
        //            return true
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "2. election started", |_, state| {
        //    for env in &state.network {
        //        if let WORegisterMsg::Internal(VPaxosMsg::M1a{..}) = env.msg {
        //            return true
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "3n. voting occurred", |_, state| {
        //    for env in &state.network {
        //        if let WORegisterMsg::Internal(VPaxosMsg::MNack{..}) = env.msg {
        //            return true
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "3. voting occurred", |_, state| {
        //    for env in &state.network {
        //        if let WORegisterMsg::Internal(VPaxosMsg::M1b{..}) = env.msg {
        //            return true
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "3a. vote registered", |_, state| {
        //    for state in &state.actor_states {
        //        if let WORegisterActorState::Server(Proposer{state : Candidate{votes}, ..}) = &**state{
        //            if votes.len() > 0 {
        //                return true
        //            }
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "3b. sufficient votes", |_, state| {
        //    for state in &state.actor_states {
        //        if let WORegisterActorState::Server(Proposer{state : Candidate{votes}, ..}) = &**state{
        //            if votes.len() > 1{
        //                return true
        //            }
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "4b. non-leader exists", |_, state| {
        //    for state in &state.actor_states {
        //        if let WORegisterActorState::Server(Proposer{state : Candidate{..}, ..}) = &**state{
        //            return true
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "4. leader elected", |_, state| {
        //    for state in &state.actor_states {
        //        if let WORegisterActorState::Server(Proposer{state : Leader{..}, ..}) = &**state{
        //            return true
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "5. value proposed", |_, state| {
        //    for env in &state.network {
        //        if let WORegisterMsg::Internal(VPaxosMsg::M2a{..}) = env.msg {
        //            return true
        //        }
        //    }
        //    false
        //})
        //.property(Expectation::Sometimes, "6. value voted for", |_, state| {
        //    for env in &state.network {
        //        if let WORegisterMsg::Internal(VPaxosMsg::M2b{..}) = env.msg {
        //            return true
        //        }
        //    }
        //    false
        //})
        .property(Expectation::Sometimes, "7. value decided", |_, state| {
            for env in &state.network {
                if let WORegisterMsg::PutOk(_) = env.msg {
                    return true
                }
            }
            false
        })
        .property(Expectation::Always, "linearizable", |_, state| {
            state.history.serialized_history().is_some()
        })
    }
}

// Rewriters

// Rewrite Id
impl Rewrite<Id> for ProposerSM {
    fn rewrite<S>(&self, plan: &RewritePlan<Id,S>) -> Self {
        match self {
            Candidate{votes} => {
                Candidate {
                    votes : votes.rewrite(plan)
                }
            }
            Leader{value, votes} => {
                Leader {
                    value : value.rewrite(plan),
                    votes : votes.rewrite(plan),
                }
            }
        }
    }
}
impl Rewrite<Id> for VPaxosActorState {
    fn rewrite<S>(&self, plan: &RewritePlan<Id,S>) -> Self {
        match self {
            Proposer{bal, state, pending_clients} => {
                Proposer{
                    bal: bal.rewrite(plan),
                    state: state.rewrite(plan),
                    pending_clients : pending_clients.clone(),
                }
            }
            Acceptor{max_bal, max_vbal} => {
                Acceptor{
                    max_bal: max_bal.rewrite(plan),
                    max_vbal: max_vbal.rewrite(plan),
                }
            }
        }
    }
}
impl Rewrite<Id> for BalNum {
    fn rewrite<S>(&self, _plan: &RewritePlan<Id,S>) -> Self {
        self.clone()
    }
}
impl<K: Hash + Eq + Clone> Rewrite<Id> for BallotNumber<K> {
    fn rewrite<S>(&self, _plan: &RewritePlan<Id,S>) -> Self {
        (*self).clone()
    }
}

impl Rewrite<Id> for VPaxosMsg {
    fn rewrite<S>(&self, _plan: &RewritePlan<Id,S>) -> Self {
        match self {
            MNack { ballot } => MNack { ballot : ballot.clone() },
            M1a { ballot } => M1a { ballot : ballot.clone() },
            M1b { ballot, last_accepted } => M1b { ballot : ballot.clone(), last_accepted : last_accepted.clone() },
            M2a { ballot, value } => M2a { ballot : ballot.clone(), value : value.clone() },
            M2b { ballot } => M2b { ballot : ballot.clone() },
        }
    }
}

// Rewrite BalNum
impl Rewrite<BalNum> for BalNum {
    fn rewrite<S>(&self, plan: &RewritePlan<BalNum, S>) -> Self {
        plan.rewrite(self)
    }
}

impl<K: Hash + Eq + Clone> Rewrite<BalNum> for BallotNumber<K> {
    fn rewrite<S>(&self, plan: &RewritePlan<BalNum,S>) -> Self {
        BallotNumber(self.0.rewrite(plan), self.1)
    }
}

impl Rewrite<BalNum> for ProposerSM {
    fn rewrite<S>(&self, plan: &RewritePlan<BalNum,S>) -> Self {
        match self {
            Candidate{votes} => {
                Candidate {
                    votes : votes.rewrite(plan)
                }
            }
            Leader{value, votes} => {
                Leader {
                    value : value.rewrite(plan),
                    votes : votes.rewrite(plan),
                }
            }
        }
    }
}

impl Rewrite<BalNum> for VPaxosActorState {
    fn rewrite<S>(&self, plan: &RewritePlan<BalNum, S>) -> Self {
        match self {
            Proposer{bal, state, pending_clients} => {
                Proposer{
                    bal: bal.rewrite(plan),
                    state: state.rewrite(plan),
                    pending_clients : pending_clients.clone(),
                }
            }
            Acceptor{max_bal, max_vbal} => {
                Acceptor{
                    max_bal: max_bal.rewrite(plan),
                    max_vbal: max_vbal.rewrite(plan),
                }
            }
        }
    }
}

impl Rewrite<BalNum> for Id {
    fn rewrite<S>(&self, _plan: &RewritePlan<BalNum, S>) -> Self {
        self.clone()
    }
}

impl<M : Rewrite<BalNum>> Rewrite<BalNum> for Envelope<M> {
    fn rewrite<S>(&self, plan: &RewritePlan<BalNum, S>) -> Self {
        let Envelope{src, dst, msg} = self;
        Envelope{ src: src.clone(), dst: dst.clone(), msg: msg.rewrite(plan)}
    }
}

impl Rewrite<BalNum> for VPaxosMsg {
    fn rewrite<S>(&self, plan: &RewritePlan<BalNum, S>) -> Self {
        match self {
            MNack { ballot } => MNack { ballot : ballot.rewrite(plan) },
            M1a { ballot } => M1a { ballot : ballot.rewrite(plan) },
            M1b { ballot, last_accepted } => M1b { ballot : ballot.rewrite(plan), last_accepted : last_accepted.rewrite(plan) },
            M2a { ballot, value } => M2a { ballot : ballot.rewrite(plan), value : value.rewrite(plan) },
            M2b { ballot } => M2b { ballot : ballot.rewrite(plan) },
        }
    }
}

// Main
fn main() -> Result<(), pico_args::Error> {

    env_logger::init_from_env(env_logger::Env::default()
        .default_filter_or("info")); // `RUST_LOG=${LEVEL}` env variable to override

    let mut args = pico_args::Arguments::from_env();
    match args.subcommand()?.as_deref() {
        Some("check-subspace") => {
            let client_count = args.opt_free_from_str()?
                .unwrap_or(2);
            let proposer_count = args.opt_free_from_str()?
                .unwrap_or(2);
            let acceptor_count = args.opt_free_from_str()?
                .unwrap_or(3);
            let channel_length = args.opt_free_from_str()?
                .unwrap_or(1);
            let cfg = VPaxosModelCfg {
                    client_count,
                    proposer_count,
                    acceptor_count,
                };
            println!("Model checking Single Shot VecPaxos with {:?} config", cfg);
            cfg.into_model()
                .within_boundary(|_,s| {
                    let lim = 3;
                    for node in &s.actor_states {
                        if let WORegisterActorState::Server(Proposer{bal, ..}) = &**node {
                            if bal.depth() > lim {
                                return false
                            }
                        }
                    }
                    true
                })
                .finite_network(FiniteNetwork::Yes(channel_length))
                .checker()
                .threads(num_cpus::get())
                .spawn_bfs_sym().report(&mut std::io::stdout());
        }
        Some("check-full") => {
            let client_count = args.opt_free_from_str()?
                .unwrap_or(2);
            let proposer_count = args.opt_free_from_str()?
                .unwrap_or(2);
            let acceptor_count = args.opt_free_from_str()?
                .unwrap_or(3);
            let channel_length = args.opt_free_from_str()?
                .unwrap_or(1);
            let cfg = VPaxosModelCfg {
                    client_count,
                    proposer_count,
                    acceptor_count,
                };
            println!("Model checking Single Shot VecPaxos with {:?} config", cfg);
            cfg.into_model()
                .finite_network(FiniteNetwork::Yes(channel_length))
                .checker()
                .threads(num_cpus::get())
                .symmetry_fn(symmetry_fn)
                .spawn_bfs_sym().report(&mut std::io::stdout());
        }
        Some("explore") => {
            let client_count = args.opt_free_from_str()?
                .unwrap_or(2);
            let proposer_count = args.opt_free_from_str()?
                .unwrap_or(2);
            let acceptor_count = args.opt_free_from_str()?
                .unwrap_or(3);
            //let channel_length = args.opt_free_from_str()?
            //    .unwrap_or(1);
            let address = args.opt_free_from_str()?
                .unwrap_or("localhost:3000".to_string());
            let cfg = VPaxosModelCfg {
                    client_count,
                    proposer_count,
                    acceptor_count,
            //        channel_length,
                };
            println!("Model checking Single Shot VecPaxos with {:?} config", cfg);
            cfg.into_model().checker()
                .threads(num_cpus::get())
                .symmetry_fn(symmetry_fn)
                .serve(address);
        }
        Some("spawn") => {
            todo!();
        }
        _ => {
            println!("USAGE:");
            println!("  ./paxos check [CLIENT_COUNT]");
            println!("  ./paxos explore [CLIENT_COUNT] [ADDRESS]");
            println!("  ./paxos spawn");
        }
    }

    Ok(())
}
