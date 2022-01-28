use serde::{Deserialize, Serialize};
use stateright::{Model, Rewrite, RewritePlan, Checker, Expectation, Representative};
use stateright::actor::{Actor, Out, Id, ActorModelState, majority, ActorModel, Envelope, DuplicatingNetwork, FiniteNetwork};
use stateright::actor::write_once_register::{WORegisterActor, WORegisterActorState, WORegisterMsg, WORegisterMsg::*};
//use stateright::semantics::write_once_register::WORegister;
//use stateright::semantics::LinearizabilityTester;
use stateright::util::{HashableHashMap, HashableHashSet};
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::{HashSet, HashMap};
use std::time::Duration;
use std::ops::Range;

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

type Value = char;
type RequestId = u64;

// Key idea
// If a ballot only exists as a dependency of other ballots, it cannot be compared against or
// re-created
// Thus that ballot can be removed without changing the state of the system

#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord)]
#[derive(Serialize, Deserialize)]
//struct Ballot(Id, HashableHashSet<Ballot>);
enum Ballot {
    Bal(Id, HashableHashSet<u64>),
    ModelBal(Id, u64),
}
use Ballot::*;
//struct Ballot(Id, Vec<u64>);

fn hash<T: Hash>(x: &T) -> u64 {
    let mut s = DefaultHasher::new();
    x.hash(&mut s);
    s.finish()
}

impl Ballot {
    // Equivalent to Bot
    fn new(id : Id) -> Self {
        Bal(id, HashableHashSet::new())
    }

    fn get<'a>(&'a self) -> (&'a Id, &'a HashableHashSet<u64>) {
        match self {
            Bal(i,v) => (i,v),
            Ballot::ModelBal(_, _) => unimplemented!(),
        }
    }

    fn mint(&self, other: &Ballot) -> Ballot {
        let mut bs = self.get().1.clone();
        bs.insert(hash(&other));
        bs.insert(hash(&self));
        Bal(self.get().0.clone(), bs)
    }

    fn depth(&self) -> usize {
        match &self {
            Bal(_, v) => v.len(),
            ModelBal(_, _) => 0,
        }
    }
}

impl PartialOrd for Ballot {

    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let self_hash = hash(&self);
        let other_hash = hash(&other);
        match (self, other) {
            _ if self.eq(other) => Some(Ordering::Equal),
            (Bal(_, _), Bal(_, v)) if v.contains(&self_hash) => Some(Ordering::Less),
            (Bal(_, v), Bal(_, _)) if v.contains(&other_hash) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn ballot_cmp() {
        use Ordering::*;
        let a0 = Ballot::new(0.into());
        let a1 = Ballot::new(1.into());

        assert_eq!(a0.partial_cmp(&a1),None);

        let b0 = a0.mint(&a1);
        let b1 = a1.mint(&a0);

        let c = b0.mint(&Ballot::new(2.into()));

        let tests = vec![
            (vec![&a0], vec![&a1], None),
            (vec![&a0], vec![&a1], None),
            (vec![&b1], vec![&b0], None),
            (vec![&b1], vec![&b0], None),

            (vec![&a0,&a1], vec![&b0,&b1], Some(Less)),
            (vec![&b0,&b1], vec![&a0,&a1], Some(Greater)),

            (vec![&c], vec![&b0, &a0, &a1], Some(Greater)),
            (vec![&c], vec![&b1], None),
        ];

        for (src, dst, exp) in tests {
            for s in &src {
                for d in &dst {
                    println!("{:?}:{:?}\n{:?}:{:?}\n----", s, hash(s), d, hash(d));
                    assert_eq!(s.partial_cmp(&d), exp)
                }
            }
        }
    }

    #[test]
    fn ballot_depth() {
        let a0 = Ballot::new(0.into());
        let a1 = Ballot::new(1.into());

        let b0 = a0.mint(&a1);
        let b1 = a1.mint(&a0);

        let c = b0.mint(&Ballot::new(2.into()));
        
        assert_eq!(a0.depth(), 0);
        assert_eq!(a1.depth(), 0);

        assert_eq!(b0.depth(), 2);
        assert_eq!(b1.depth(), 2);

        assert_eq!(c.depth(), 4);
    }
}

//#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord)]
//#[derive(Serialize, Deserialize)]
//enum Ballot {
//    Bot,
//    Bal(Id, Box<Ballot>),
//}
//
//impl Ballot {
//    fn mint(&self, id : Id) -> Ballot {
//        Bal(id, Box::new(self.clone()))
//    }
//}

//impl PartialOrd for Ballot  {
//
//    fn lt(&self, other: &Self) -> bool {
//        match (self.clone(), other.clone()) {
//            (_, Bot) => { false }, 
//            (s, o) if s == o => { false },
//            (Bot, _) => { true }
//            (s, Bal(_, o) ) => s == *o || s.lt(&*o)
//        }
//    }
//
//    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//        if self.eq(other) {
//            Some(Ordering::Equal)
//        } else if self.lt(other)  {
//            Some(Ordering::Less)
//        } else if other.lt(self)  {
//            Some(Ordering::Greater)
//        } else { None }
//    }
//}
//use Ballot::*;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[derive(Serialize, Deserialize)]
enum VPaxosMsg {
    MNack { ballot: Ballot },

    M1a   { ballot: Ballot },
    M1b   { ballot: Ballot, last_accepted: Option<(Ballot, Value)> },

    M2a   { ballot: Ballot, value: Value },
    M2b   { ballot: Ballot },
}
use VPaxosMsg::*;

#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
enum ProposerSM {
    Follower,
    Candidate{votes : HashableHashMap<Id, Option<(Ballot, Value)>>},
    Leader{value : Option<Value>, votes : HashableHashSet<Id>}, // Chosen value and vector of votes
}
use ProposerSM::*;

#[derive(Clone, Debug, Hash, PartialEq, PartialOrd, Eq, Ord)]
enum ClientMsg {
    Put(Id, u64, Value),
    Get(Id, u64),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
enum VPaxosActorState {
    Proposer {
        bal: Ballot,
        state: ProposerSM,
        pending_clients: Vec<ClientMsg>,
    },
    Acceptor{
        max_bal: Ballot,
        max_vbal: Option<(Ballot, Value)>,
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

fn select_value(ballots: Vec<Option<(Ballot, Value)>>) -> Option<Value> {
    let res = ballots.into_iter()
        .filter_map(|v| v)
        .max_by_key(|(b,_)| b.clone());
    match res {
        None => { None },
        Some((_,v)) => { Some(v) }
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
            VPaxosKind::Proposer => Proposer{bal : Ballot::new(id), state : Candidate{votes: HashableHashMap::new()}, pending_clients : vec![]},
            VPaxosKind::Acceptor => Acceptor{max_bal : Ballot::new(0.into()), max_vbal : None},
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
            Proposer{state : Candidate{votes}, bal, pending_clients} if votes.len() >= majority(self.acceptor_ids.len()) => {
                let values : Vec<Option<(Ballot,Value)>> = votes.iter()
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
                *state.to_mut() = Proposer{
                    bal: bal.clone(),
                    state: Leader{value : new_value, votes : HashableHashSet::new()},
                    pending_clients : pending_clients.clone()
                };
            },
            // Transmit 1a messages
            Proposer{state : Candidate{ .. }, bal, ..} => {
                let msg = Internal(M1a{ballot : bal.clone()});
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
                let msg = Internal(M2a{ballot : bal.clone(), value: value.clone()});
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
                if !(max_bal <= mbal) => {
                o.send(src, Internal(MNack{ballot : max_bal.clone()}));
            }
            // If a nack is received for a ballot which is not less than the current one
            (Proposer{bal, pending_clients, ..}, Internal( MNack{ballot : mbal} )) if !(mbal < bal) => {
                let new_bal = bal.mint(mbal);
                *state.to_mut() = Proposer{bal : new_bal.clone(), state: Candidate{votes : HashableHashMap::new()}, pending_clients: pending_clients.clone()};
            }
            // ~Phase1b(a)
            (Acceptor{max_bal, max_vbal}, Internal(M1a{ballot : mbal})) if max_bal <= mbal => {
                o.send(src, Internal(M1b{ballot : mbal.clone(), last_accepted : max_vbal.clone()}));
                *state.to_mut() = Acceptor{max_bal : mbal.clone(), max_vbal : max_vbal.clone()};
            }
            // ~Phase1b.2(p) necessary since cannot just do \E M \subset msgs: quorum(1b, acceptors, M, ballot)
            (Proposer{bal, state : Candidate{votes}, pending_clients}, Internal(M1b{ballot: mbal, last_accepted})) if bal == mbal => {
                let mut votes = votes.clone();
                votes.insert(src, last_accepted.clone());
                *state.to_mut() = Proposer{bal: bal.clone(), state: Candidate{votes}, pending_clients: pending_clients.clone()}
            }
            // ~Phase2b(a)
            (Acceptor{max_bal, ..}, Internal(M2a{ballot: mbal, value})) if max_bal <= &mbal => {
                *state.to_mut() = Acceptor{max_bal : mbal.clone(), max_vbal : Some((mbal.clone(), value.clone()))};
                let msg = Internal(M2b{ballot : mbal.clone()});
                o.send(src, msg);
            }
            // ~Phase3(p) receive phase2b message and decide value
            (Proposer{bal, state : Leader{value, votes}, pending_clients}, Internal(M2b{ballot : mbal})) if bal == mbal => {
                let mut votes = votes.clone();
                votes.insert(src); 
                *state.to_mut() = Proposer{
                    bal : bal.clone(),
                    state: Leader{value : *value, votes},
                    pending_clients : pending_clients.clone()
                };
            }
            (Proposer{bal, state : p_state, pending_clients}, Put(rid, put_value)) => {
                let mut p_state = p_state.clone();
                if let Leader{value: None, votes} = p_state {
                    let msg = Internal(M2a{ballot : bal.clone(), value: *put_value});
                    o.broadcast(&self.acceptor_ids, &msg);
                    p_state = Leader{value: Some(*put_value), votes : votes.clone()};
                };
                let mut pending_clients = pending_clients.clone();
                pending_clients.push(ClientMsg::Put(src, *rid, *put_value));
                *state.to_mut() = Proposer{
                    bal: bal.clone(),
                    pending_clients,
                    state : p_state,
                };
            },
            (Proposer{bal, state : p_state, pending_clients}, Get(rid)) => {
                let mut pending_clients = pending_clients.clone();
                pending_clients.push(ClientMsg::Get(src, *rid));
                *state.to_mut() = Proposer{
                    bal: bal.clone(),
                    pending_clients,
                    state : p_state.clone(),
                };
            },
            _ => {}
        }
    }
}


fn normalise_ballot(b : &Ballot, active_ballots : &HashSet<u64>) -> Ballot {
    let mut hasher = DefaultHasher::new();
    for bal in b.get().1 {
        if !active_ballots.contains(bal) {
            bal.hash(&mut hasher)
        }
    };
    ModelBal(
        b.get().0.clone(),
        hasher.finish(),
    )
}

fn all_ballots<H>(state : &ActorModelState<WORegisterActor<VPaxosActor>, H>) -> HashSet<&Ballot> {
    use WORegisterActorState::*;
    let mut active_ballots = HashSet::<&Ballot>::new();
    // Add all used ballots from nodes
    for node in &state.actor_states {
        match &**node {
            Server(Proposer{state : Candidate{votes}, bal, ..}) => { 
                active_ballots.insert(bal);
                for (_, vote) in votes.into_iter() {
                    match vote {
                        None => {}
                        Some((b,_)) => { active_ballots.insert(b); }
                    };
                };
            }
            // Just follower and leader remain
            Server(Acceptor {max_bal: bal, max_vbal : None}) |
            Server(Proposer {bal, .. }) => { active_ballots.insert(bal); },
            Server(Acceptor {max_bal, max_vbal : Some((max_vbal, _))}) => { 
                active_ballots.insert(max_bal);
                active_ballots.insert(max_vbal);
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
                => { active_ballots.insert(ballot); }
            WORegisterMsg::Internal(M1b{ ballot, last_accepted : Some((la_bal, _)) }) => { 
                active_ballots.insert(ballot);
                active_ballots.insert(la_bal);
            }
            _ => {}
        }
    };
    active_ballots
}

fn symmetry_fn<H: Clone + 'static + Rewrite<Id>>(state : &ActorModelState<WORegisterActor<VPaxosActor>,H>) -> ActorModelState<WORegisterActor<VPaxosActor>,H> 
{
    let active_ballots = all_ballots(state);
    let active_ballot_hashes = active_ballots.iter().map(|b| hash(b)).collect();
    let mut ballot_mapping = HashMap::<Ballot, Ballot>::new();
    for &bal in &active_ballots {
        ballot_mapping.insert(bal.clone(), normalise_ballot(&bal, &active_ballot_hashes));
    }
    let ballot_rewrite_plan : RewritePlan<Ballot, _> = RewritePlan::new(
        ballot_mapping,
        |r, s| {
            s.get(r).unwrap().clone()
        }
    );
    let canonicalised = ActorModelState {
        actor_states : state.actor_states.rewrite(&ballot_rewrite_plan),
        network : state.network.rewrite(&ballot_rewrite_plan),
        .. (state.clone())
    };
    canonicalised.representative()
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
            ()>//LinearizabilityTester<Id,WORegister<Value>>>
    {
        //let proposer_ids : Vec<Id> = (0..self.proposer_count)
        //    .map(|x| x.into())
        //    .collect();
        let acceptor_ids : Vec<Id> = (self.proposer_count..(self.proposer_count + self.acceptor_count))
            .map(|x| x.into())
            .collect();
        ActorModel::new(
            self.clone(),
            ())//LinearizabilityTester::new(WORegister(None)))
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
        .property(Expectation::Sometimes, "1 received vote", |_, state| {
            for env in &state.network {
                if let WORegisterMsg::Internal(VPaxosMsg::MNack{..}) = env.msg {
                    if env.dst == 1.into() {
                        return true
                    }
                }
            }
            false
        })
//        .property(Expectation::Sometimes, "1. value sent", |_, state| {
//            for env in &state.network {
//                if let WORegisterMsg::Put(_,_) = env.msg {
//                    return true
//                }
//            }
//            false
//        })
//        .property(Expectation::Sometimes, "2. election started", |_, state| {
//            for env in &state.network {
//                if let WORegisterMsg::Internal(VPaxosMsg::M1a{..}) = env.msg {
//                    return true
//                }
//            }
//            false
//        })
//        .property(Expectation::Sometimes, "3. voting occurred", |_, state| {
//            for env in &state.network {
//                if let WORegisterMsg::Internal(VPaxosMsg::M1b{..}) = env.msg {
//                    return true
//                }
//            }
//            false
//        })
//        .property(Expectation::Sometimes, "3a. vote registered", |_, state| {
//            for state in &state.actor_states {
//                if let WORegisterActorState::Server(Proposer{state : Candidate{votes}, ..}) = &**state{
//                    if votes.len() > 0 {
//                        return true
//                    }
//                }
//            }
//            false
//        })
//        .property(Expectation::Sometimes, "3b. sufficient votes", |_, state| {
//            for state in &state.actor_states {
//                if let WORegisterActorState::Server(Proposer{state : Candidate{votes}, ..}) = &**state{
//                    if votes.len() > 0 {
//                        return true
//                    }
//                }
//            }
//            false
//        })
//        .property(Expectation::Sometimes, "4. leader elected", |_, state| {
//            for state in &state.actor_states {
//                if let WORegisterActorState::Server(Proposer{state : Leader{..}, ..}) = **state{
//                    return true
//                }
//            }
//            false
//        })
//        .property(Expectation::Sometimes, "5. value proposed", |_, state| {
//            for env in &state.network {
//                if let WORegisterMsg::Internal(VPaxosMsg::M2a{..}) = env.msg {
//                    return true
//                }
//            }
//            false
//        })
        .property(Expectation::Sometimes, "6. value voted for", |_, state| {
            for env in &state.network {
                if let WORegisterMsg::Internal(VPaxosMsg::M2b{..}) = env.msg {
                    return true
                }
            }
            false
        })
        .property(Expectation::Sometimes, "7. value decided", |_, state| {
            for env in &state.network {
                if let WORegisterMsg::PutOk(_) = env.msg {
                    return true
                }
            }
            false
        })
        //.property(Expectation::Always, "linearizable", |_, state| {
        //    state.history.serialized_history().is_some()
        //})
    }
}

// Rewriters
impl Rewrite<Id> for ProposerSM {
    fn rewrite<S>(&self, plan: &RewritePlan<Id,S>) -> Self {
        match self {
            Follower => Follower,
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
impl Rewrite<Id> for Ballot {
    fn rewrite<S>(&self, _plan: &RewritePlan<Id,S>) -> Self {
        self.clone()
    }
}

impl Rewrite<Ballot> for ProposerSM {
    fn rewrite<S>(&self, plan: &RewritePlan<Ballot,S>) -> Self {
        match self {
            Follower => Follower,
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
impl Rewrite<Ballot> for VPaxosActorState {
    fn rewrite<S>(&self, plan: &RewritePlan<Ballot,S>) -> Self {
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
impl Rewrite<Ballot> for Id {
    fn rewrite<S>(&self, _plan: &RewritePlan<Ballot,S>) -> Self {
        self.clone()
    }
}
impl<M : Rewrite<Ballot>> Rewrite<Ballot> for Envelope<M> {
    fn rewrite<S>(&self, plan: &RewritePlan<Ballot,S>) -> Self {
        let Envelope{src, dst, msg} = self;
        Envelope{ src: src.clone(), dst: dst.clone(), msg: msg.rewrite(plan)}
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

impl Rewrite<Ballot> for VPaxosMsg {
    fn rewrite<S>(&self, plan: &RewritePlan<Ballot,S>) -> Self {
        match self {
            MNack { ballot } => MNack { ballot : ballot.rewrite(plan) },
            M1a { ballot } => M1a { ballot : ballot.rewrite(plan) },
            M1b { ballot, last_accepted } => M1b { ballot : ballot.rewrite(plan), last_accepted : last_accepted.rewrite(plan) },
            M2a { ballot, value } => M2a { ballot : ballot.rewrite(plan), value : value.rewrite(plan) },
            M2b { ballot } => M2b { ballot : ballot.rewrite(plan) },
        }
    }
}

impl Rewrite<Ballot> for Ballot {
    fn rewrite<S>(&self, plan: &RewritePlan<Ballot, S>) -> Self {
        plan.rewrite(self)
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
                    let lim = 2;
                    for node in &s.actor_states {
                        if let WORegisterActorState::Server(Proposer{bal, ..}) = &**node {
                            if bal.depth() >= lim {
                                return false
                            }
                        }
                    }
                    true
                })
                .finite_network(FiniteNetwork::Yes(channel_length))
                .checker()
                .threads(num_cpus::get())
                .symmetry_fn(symmetry_fn)
                .spawn_dfs().report(&mut std::io::stdout());
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
                .spawn_dfs().report(&mut std::io::stdout());
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
