/*
 * Two-phase commit protocol -- no failures, safety only
 *
 * (TODO Manos provide slide link. Slides are on the web, but only behind a sleazy scraper site.)
 *
 * 2-Phase Commit Protocol english design doc:
 *
 * 1, Coordinator sends VOTE-REQ to all participants.
 * 2. Each participant i sends back vote_i to coordinator.
 *   If vote_i=No then i sets decision_i := Abort.
 * 3. Coordinator collects votes.
 *   If all votes are yes then coordinator sets decision_c := Commit and sends Commit to all participants.
 *   Else coordinator sets decision_c := Abort and sends Abort to all participants who voted yes.
 * 4. Participants receiving Commit set decision_i := Commit
 *   (The slide is delightfully poorly specified. "else decision_i := Abort"!? When else? As soon as
 *   it doesn't hear Commit!?)
 *
 * 2PC should satisfy the Atomic Commit specification. English design doc:
 *
 * Modeling suggestions:
 *
 * Model the Coordinator and Participants as separate host types, since they
 * have unrelated state & behavior.
 *
 * Model the Participants as each having a constant preferred value that
 * they'll vote for; 2PC learns whether the Participants all prefer a Yes vote.
 *
 * Because we're assuming no host failure, the coordinator can simply wait
 * until every vote has been cast to compute its decision.
 * Don't bother optimizing for the case where an abort has been voted and hence
 * the coordinator doesn't really need to wait for every vote.
 *
 * After building the model, define the Safety predicate as AC1 && AC3 && AC4, then prove
 * it inductive by adding invariants and fixing bugs in your 2PC protocol model.
 */

include "../../library/library.dfy"
include "atomic-commit-spec.dfy"

//#instructor Player 1 -- but we're not going to expose that distinction yet
module NetIfc {
  import opened Library
  import opened Types
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

module Network {
  import opened Types
  import opened NetIfc

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

//#instructor Player 2
module CoordinatorHost {
  import opened Types
  import opened Library
  import opened NetIfc

  datatype Constants = Constants(hostCount: nat)
  datatype Variables = Variables(votes: seq<Option<Vote>>, decision: Option<Decision>)
  {
    predicate WF(c: Constants) {
      && |votes| == c.hostCount
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    // No votes recorded yet
    && (forall hostIdx:ParticipantId | hostIdx < |v.votes| :: v.votes[hostIdx].None?)
    // No decision recorded yet
    && v.decision.None?
  }

  // Protocol steps

  predicate SendReq(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps == MessageOps(None, Some(VoteReqMsg))
    && v' == v  // UNCHANGED everything.
  }

  predicate LearnVote(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.VoteMsg?
    && recvMsg.sender < c.hostCount
    // Record sender's vote.
    && v' == v.(votes := v.votes[recvMsg.sender := Some(recvMsg.vote)])
    && msgOps.send.None?
  }

  predicate AllVotesCollected(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall hostIdx:ParticipantId | hostIdx < |v.votes| :: v.votes[hostIdx].Some?)
  }

  predicate ObservesResult(c: Constants, v: Variables, decision: Decision)
  {
    && v.WF(c)
    && AllVotesCollected(c, v)
    && decision ==
      if (forall hostIdx:ParticipantId | hostIdx < |v.votes| :: v.votes[hostIdx].value.Yes?)
      then Commit
      else Abort
  }

  predicate Decide(c: Constants, v: Variables, v': Variables, decision: Decision, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && msgOps.recv.None?
    && ObservesResult(c, v, decision)
    // Record the decision
    && v' == v.(decision := Some(decision))
    // Transmit the decision
    && msgOps.send == Some(DecisionMsg(decision))
  }

  // JayNF
  datatype Step =
    | SendReqStep
    | LearnVoteStep
    | DecideStep(decision: Decision)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case SendReqStep => SendReq(c, v, v', msgOps)
      case LearnVoteStep => LearnVote(c, v, v', msgOps)
      case DecideStep(decision) => Decide(c, v, v', decision, msgOps)
  }

  // msgOps is a "binding variable" -- the host and the network have to agree on its assignment
  // to make a valid transition. So the host explains what would happen if it could receive a
  // particular message, and the network decides whether such a message is available for receipt.
  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

module ParticipantHost {
  import opened Types
  import opened Library
  import opened NetIfc

  datatype Constants = Constants(hostId: ParticipantId, preference: Vote)
  datatype Variables = Variables(decision: Option<Decision>)

  predicate Vote(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.VoteReqMsg?
    && msgOps.send == Some(VoteMsg(c.hostId, c.preference))
    // Infer Abort decision if we're voting No
    && v'.decision == if c.preference.No? then Some(Abort) else v.decision
  }

  predicate LearnDecision(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.DecisionMsg?
    && v'.decision == Some(recvMsg.decision)
    && msgOps.send.None?
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.decision.None?
  }

  // JayNF
  datatype Step =
    | VoteStep
    | LearnDecisionStep

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case VoteStep => Vote(c, v, v', msgOps)
      case LearnDecisionStep => LearnDecision(c, v, v', msgOps)
  }

  // msgOps is a "binding variable" -- the host and the network have to agree on its assignment
  // to make a valid transition. So the host explains what would happen if it could receive a
  // particular message, and the network decides whether such a message is available for receipt.
  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

//#instructor Player 1
module DistributedSystem {
  import opened Types
  import opened NetIfc
  import CoordinatorHost
  import ParticipantHost
  import Network

  datatype Constants = Constants(
    coordinator: CoordinatorHost.Constants,
    participants: seq<ParticipantHost.Constants>,
    network: Network.Constants)
  {
    predicate WF() {
      // Coordinator knows how many participants to expect votes from
      && coordinator.hostCount == |participants|
      // Participants know their own ids
      && (forall idx | 0<=idx<|participants| :: participants[idx].hostId == idx)
      // Note we *DON'T* specify partipants' preference fields; that's the
      // degree of freedom that gives the protocol something to do.
    }
    predicate ValidParticipantId(id: ParticipantId) {
      id < |participants|
    }
  }

  datatype Variables = Variables(
    coordinator: CoordinatorHost.Variables,
    participants: seq<ParticipantHost.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && |participants| == |c.participants|
      && coordinator.WF(c.coordinator)
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && c.WF()
    && v.WF(c)
    && CoordinatorHost.Init(c.coordinator, v.coordinator)
    && (forall idx:nat | c.ValidParticipantId(idx) :: ParticipantHost.Init(c.participants[idx], v.participants[idx]))
    && Network.Init(c.network, v.network)
  }

  predicate Coordinator(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
    // all participants UNCHANGED
    && (forall idx:nat | c.ValidParticipantId(idx) :: v'.participants[idx] == v.participants[idx])
  }

  predicate Participant(c: Constants, v: Variables, v': Variables, idx: ParticipantId, msgOps: MessageOps)
  {
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && c.ValidParticipantId(idx)
    && ParticipantHost.Next(c.participants[idx], v.participants[idx], v'.participants[idx], msgOps)
    // all other participants UNCHANGED
    && (forall otherIdx:nat | c.ValidParticipantId(otherIdx) && otherIdx != idx :: v'.participants[otherIdx] == v.participants[otherIdx])
    // coordinator UNCHANGED
    && v'.coordinator == v.coordinator
  }

  // JayNF
  datatype Step =
    | CoordinatorStep(msgOps: MessageOps)
    | ParticipantStep(idx: ParticipantId, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && (
      match step
        case CoordinatorStep(msgOps) => Coordinator(c, v, v', msgOps)
        case ParticipantStep(idx, msgOps) => Participant(c, v, v', idx, msgOps)
      )
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

module Proof {
  import opened Types
  import opened Library
  import opened DistributedSystem

  predicate AllWithDecisionAgreeWithThisOne(c: Constants, v: Variables, decision: Decision)
    requires c.WF()
    requires v.WF(c)
    // I pulled this conjunction into a named predicate because Dafny warned of
    // no trigger for the exists.
  {
    && (v.coordinator.decision.Some? ==> v.coordinator.decision.value == decision)
    && (forall idx:ParticipantId
      | c.ValidParticipantId(idx) && v.participants[idx].decision.Some?
      :: v.participants[idx].decision.value == decision)
  }

  predicate VoteMessagesAgreeWithParticipantPreferences(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.VoteMsg?
      && c.ValidParticipantId(msg.sender)
      :: msg.vote == c.participants[msg.sender].preference
    )
  }

  predicate CoordinatorStateSupportedByVote(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    (forall idx:ParticipantId |
      && c.ValidParticipantId(idx)
      && v.coordinator.votes[idx].Some?
      :: VoteMsg(idx, v.coordinator.votes[idx].value) in v.network.sentMsgs
    )
  }

  predicate DecisionMsgsAgreeWithDecision(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.DecisionMsg?
      :: CoordinatorHost.ObservesResult(c.coordinator, v.coordinator, msg.decision)
    )
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && c.WF()
    && v.WF(c)
    && VoteMessagesAgreeWithParticipantPreferences(c, v)
    && CoordinatorStateSupportedByVote(c, v)
    && DecisionMsgsAgreeWithDecision(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
    // Nobody has agreed with anything yet, so they agree with both.
    assert AllWithDecisionAgreeWithThisOne(c, v, Commit); // witness.
    assert AllWithDecisionAgreeWithThisOne(c, v, Abort); // witness.
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    // The body of this lemma got really big (expanding foralls, case splits,
    // testing asserts) while I was figuring out what invariants were missing
    // ... and fixing a couple of errors in the protocol definition itself.
    // Afterward, nearly all of that text could be deleted.
    var step :| NextStep(c, v, v', step);   // Witness
    assert Safety(c, v');
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}

abstract module RefinementTheorem {
  import opened Types
  import opened Library
  import opened DistributedSystem
  import AtomicCommit

  function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants

  function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables

  predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    requires DistributedSystem.Init(c, v)
    ensures Inv(c, v)
    ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables)
    requires DistributedSystem.Next(c, v, v')
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'))

}

module RefinementProof refines RefinementTheorem {
  import opened Types
  import opened Library
  import opened DistributedSystem
  import opened AtomicCommit

  function ConstantsAbstraction(constants: DistributedSystem.Constants) : AtomicCommit.Constants
  {
    
  }
}
