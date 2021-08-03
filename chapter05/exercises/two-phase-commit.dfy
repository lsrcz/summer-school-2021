/*
 * Two-phase commit protocol -- no failures, safety only
 *
 * (TODO Manos provide slide link. Slides are on the web, but only behind a sleazy scraper site.)
 *
 * Coordinator sends VOTE-REQ to all participants.
 * Each participant i sends back vote_i to coordinator.
 *   If vote_i=No then i sets decision_i := Abort.
 * Coordinator collects votes.
 *   If all votes are yes then coordinator sets decision_c := Commit and sends Commit to all participants.
 *   Else coordinator sets decision_c := Abort and sends Abort to all participants who voted yes.
 * Participants receiving Commit set decision_i := Commit
 *   (The slide is delightfully poorly specified. "else decision_i := Abort"!? When else? As soon as
 *   it doesn't hear Commit!?)
 *
 * Model the Coordinator and Participants as separate host types, since they have unrelated state & behavior.
 * Model the Participants as each having a constant preferred value that they'll vote for; 2PC learns
 * whether the Participants all prefer a Yes vote.
 * Because we're assuming no host failure, the coordinator can simply wait until every vote has been
 * cast to compute its decision.
 */

include "../../library/library.dfy"

// Player 2
module Types {
  type ParticipantId = nat

  datatype Vote = Yes | No
  datatype Decision = Commit | Abort

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
    | VoteReqMsg                           // from leader
    | VoteMsg(sender: ParticipantId, vote: Vote)  // from participant
    | DecisionMsg(decision: Decision)
}

// Player 1
module NetIfc {
  import opened Library
  import opened Types
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

// Player 2
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

  // Pulled into predicate to mention from proof
  predicate ObservesResult(c: Constants, v: Variables, decision: Decision)
  {
    // We have heard from all participants.
    && (forall hostIdx:ParticipantId | hostIdx < |v.votes| :: v.votes[hostIdx].Some?)
    // Compute the decision (all Yes -> Commit)
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

  predicate AllAgreeWithDecision(c: Constants, v: Variables, decision: Decision)
    requires c.WF()
    requires v.WF(c)
    // I pulled this conjunction into a named predicate because Dafny warned of
    // no trigger for the exists.
  {
    && (v.coordinator.decision.Some? ==> v.coordinator.decision.value == decision)
    && (forall idx:ParticipantId | c.ValidParticipantId(idx) && v.participants[idx].decision.Some?
      :: v.participants[idx].decision.value == decision)
  }

  predicate Safety(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    // There's some decision everybody can agree on.
    exists decision :: AllAgreeWithDecision(c, v, decision)
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

  predicate CoordinatorStateAgreesWithParticipantPreferences(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    (forall idx:ParticipantId |
      && c.ValidParticipantId(idx)
      && v.coordinator.votes[idx].Some?
      :: v.coordinator.votes[idx].value == c.participants[idx].preference
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
    && CoordinatorStateAgreesWithParticipantPreferences(c, v)
    && DecisionMsgsAgreeWithDecision(c, v)
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
    // Nobody has agreed with anything yet, so they agree with both.
    assert AllAgreeWithDecision(c, v, Commit); // witness.
    assert AllAgreeWithDecision(c, v, Abort); // witness.
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    var step :| NextStep(c, v, v', step);

    forall msg |
      && msg in v'.network.sentMsgs
      && msg.VoteMsg?
      && c.ValidParticipantId(msg.sender)
      ensures msg.vote == c.participants[msg.sender].preference
    {
      if step.CoordinatorStep? {
        var coordinatorStep :| CoordinatorHost.NextStep(c.coordinator, v.coordinator, v'.coordinator, coordinatorStep, step.msgOps);
        assert Some(msg) != step.msgOps.send;
        assert msg in v.network.sentMsgs;
        assert msg.vote == c.participants[msg.sender].preference;
      } else {
        assume false;
        var participantStep :| ParticipantHost.NextStep(c.participants[step.idx], v.participants[step.idx], v'.participants[step.idx], participantStep, step.msgOps);
        assert msg in v.network.sentMsgs;
        assert msg.vote == c.participants[msg.sender].preference;
      }
    }

    assert VoteMessagesAgreeWithParticipantPreferences(c, v');
    assume DecisionMsgsAgreeWithDecision(c, v');
    assume Safety(c, v');
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
