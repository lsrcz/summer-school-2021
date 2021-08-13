//#title Two Phase Commit Model
//#desc Model a distributed protocol using compound state machines.

/*
 * 2-Phase Commit Protocol english design doc:
 *
 * 1, Coordinator sends VOTE-REQ to all participants.
 * 2. Each participant i sends back vote_i to coordinator.
 *   If vote_i=No then i sets decision_i := Abort.
 * 3. Coordinator collects votes.
 *   If all votes are yes then coordinator sets decision_c := Commit and sends
 *   Commit to all participants.
 *   Else coordinator sets decision_c := Abort and sends Abort to all
 *   participants who voted yes.
 * 4. Participants receiving Commit set decision_i := Commit
 *   (The slide is delightfully poorly specified. "else decision_i := Abort"!?
 *   When else? As soon as it doesn't hear Commit!?)
 */

include "../../library/library.dfy" // Some handy utilities.

// Environment models assumptions about the network and the DistributedSystem -- the
// relationship among the participating hosts.
include "../../library/Environment.dfy"

module Types {
  type HostId = nat
  datatype Vote = Yes | No
  datatype Decision = Commit | Abort

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
    | VoteReqMsg                           // from leader
    | VoteMsg(sender: HostId, vote: Vote)  // from participant
    | DecisionMsg(decision: Decision)

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

// Dafny module refinement: NetIfc is defined in Environment, but it has a
// placeholder (parameter) type for "Message." So we supply that here to
// get the MessageOps types expected by the Network and DistributedSystem
// modules.
module TwoPCNetIfc refines NetIfc {
  import TwoPCTypes
  type Message = TwoPCTypes.Message
}

// There are two host roles in 2PC, Coordinator and Participant. We'll define
// separate state machines for each.
module CoordinatorHost {
  import opened TwoPCTypes
  import opened Library
  import opened TwoPCNetIfc

  datatype Constants = Constants(participantCount: nat)
  datatype Variables = Variables(votes: seq<Option<Vote>>, decision: Option<Decision>)
  {
    predicate WF(c: Constants) {
      && |votes| == c.participantCount
    }
  }

  predicate Init(c: Constants, v: Variables, participantCount: nat)
  {
    && v.WF(c)
    // ProtocolHostsInit tells us what participantCount to expect.
    && c.participantCount == participantCount
    // No votes recorded yet
    && (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].None?)
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
    && recvMsg.sender < c.participantCount
    // Record sender's vote.
    && v' == v.(votes := v.votes[recvMsg.sender := Some(recvMsg.vote)])
    && msgOps.send.None?
  }

  predicate AllVotesCollected(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].Some?)
  }

  predicate ObservesResult(c: Constants, v: Variables, decision: Decision)
  {
    && v.WF(c)
    && AllVotesCollected(c, v)
    && decision ==
      if (forall hostIdx:HostId | hostIdx < |v.votes| :: v.votes[hostIdx].value.Yes?)
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
  import opened TwoPCTypes
  import opened Library
  import opened TwoPCNetIfc

  datatype Constants = Constants(hostId: HostId, preference: Vote)
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

  predicate Init(c: Constants, v: Variables, hostId: HostId)
  {
    && v.decision.None?
    // ProtocolHostsInit tells us what our own hostId is so we can
    // set the return address on outgoing messages.
    && c.hostId == hostId
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

// The DistributedSystem model in Environment only accounts for one notion of
// Host, so we define a generic Host type that's either Coordinator or Participant.
module Host refines HostIfc {
  import opened Library
  import CoordinatorHost
  import ParticipantHost
  import NI = TwoPCNetIfc

  datatype Constants =
    | CoordinatorConstants(coordinator: CoordinatorHost.Constants)
    | ParticipantConstants(participant: ParticipantHost.Constants)

  datatype Variables =
    | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
    | ParticipantVariables(participant: ParticipantHost.Variables)
  {
    predicate WF(c: Constants) {
      && CoordinatorVariables? <==> c.CoordinatorConstants? // types of c & v agree
    }
  }

  // Dispatch Next to appropriate underlying implementation.
  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: NI.MessageOps)
  {
    && v.WF(c)
    && match c
      case CoordinatorConstants(_) => CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
      case ParticipantConstants(_) => ParticipantHost.Next(c.participant, v.participant, v'.participant, msgOps)
  }
}

// TODO(jonh): would like to remove 'abstract' here, but public Dafny's module
// system is bonkers.
abstract module TwoPCDistributedSystem refines DistributedSystem {
  import opened Library
  import HostIfc = Host

  // Protocol requires one coordinator and the rest participants;
  // coordinator must know how many participants, and participants must know own ids.
  predicate ProtocolHostsInit(c: Constants, v: Variables)
  {
    // Last host is a coordinator, and is inittid to know about the N-1 participants.
    && Last(c.hosts).CoordinatorHost?
    && CoordinatorHost.Init(Last(c.hosts).c, Last(v.hosts).v, |c.hosts|-1)
    // All the others are participants
    && (forall hostid | 0 <= hostid < |c.hosts|-1 ::
        && c.hosts[hostid].c.ParticipantHost?
        && ParticipantHost.Init(c.hosts[hostid].v, v.hosts[hostid].v, hostid)
      )
  }
}
