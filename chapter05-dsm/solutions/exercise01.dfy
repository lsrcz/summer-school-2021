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
  import opened Library

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

// There are two host roles in 2PC, Coordinator and Participant. We'll define
// separate state machines for each.
module CoordinatorHost {
  import opened Types
  import opened Library

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
  import opened Types
  import opened Library

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

// Define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
module Host {
  import opened Library
  import opened Types
  import CoordinatorHost
  import ParticipantHost

  datatype Constants =
    | CoordinatorConstants(coordinator: CoordinatorHost.Constants)
    | ParticipantConstants(participant: ParticipantHost.Constants)

  datatype Variables =
    | CoordinatorVariables(coordinator: CoordinatorHost.Variables)
    | ParticipantVariables(participant: ParticipantHost.Variables)
  {
    predicate WF(c: Constants) {
      && (CoordinatorVariables? <==> c.CoordinatorConstants?) // types of c & v agree
    }
  }

  // Dispatch Next to appropriate underlying implementation.
  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case CoordinatorConstants(_) => CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps)
      case ParticipantConstants(_) => ParticipantHost.Next(c.participant, v.participant, v'.participant, msgOps)
      )
  }
}

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
module Network {
  import opened Types

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

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
abstract module DistributedSystem {
  import opened Library
  import opened Types
  import Network
  import Host
  import CoordinatorHost
  import ParticipantHost

  datatype Constants = Constants(
    hosts: seq<Host.Constants>,
    network: Network.Constants)
  {
    predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && 0 < |c.hosts|  // at least a coordinator
      && |hosts| == |c.hosts|
    }
  }

  // ProtocolHostsInit is the only part of this module supplied by the protocol
  // definition.
  // This interface gives the specific protocol an opportunity to
  // set up constraints across the various hosts.
  // Protocol requires one coordinator and the rest participants;
  // coordinator must know how many participants, and participants must know own ids.
  predicate ProtocolHostsInit(c: Constants, v: Variables)
  {
    // variables are well-formed (same number of host slots as constants expect)
    && v.WF(c)
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |c.hosts| ::
        v.hosts[hostid].WF(c.hosts[hostid]))
    // Last host is a coordinator, and is inittid to know about the N-1 participants.
    && Last(c.hosts).CoordinatorConstants?
    && CoordinatorHost.Init(Last(c.hosts).coordinator, Last(v.hosts).coordinator, |c.hosts|-1)
    // All the others are participants
    && (forall hostid:HostId | hostid < |c.hosts|-1 ::
        && c.hosts[hostid].ParticipantConstants?
        && ParticipantHost.Init(c.hosts[hostid].participant, v.hosts[hostid].participant, hostid)
      )
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && ProtocolHostsInit(c, v)
    && Network.Init(c.network, v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && v.WF(c)
    && v'.WF(c)
    && HostAction(c, v, v', step.hostid, step.msgOps)
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}
