/*
 * Single-instance 2PC.
 */

include "../../library/library.dfy"

// Player 2
module Types {
  type HostId = nat

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
    | ProposeReqMsg(leader: nat)   // from leader
    | ProposeAckMsg(leader:nat, follower: nat, accept: bool) // from follower
    | AbortMsg(leader: nat)        // from leader
    | CommitMsg(leader: nat)       // from leader
}

// Player 1
module NetIfc {
  import opened Library
  import opened Types
  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}

// Player 2
module Host {
  import opened Types
  import opened Library
  import opened NetIfc

  datatype Constants = Constants(id: HostId, hostCount: nat)
  datatype Variables = Variables(
    // Follower state
    proposed: Option<HostId>, // a proposed value locked at this host
    leader: Option<HostId>,   // a committed result

    // Leader state
    hasLead: bool,           // I only ever get to propose once
    locks: set<HostId>        // who has acked my proposal
    )

  predicate SendProposeReq(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Can't start the protocol if
    // * we already started a protocol (and may even have aborted, so
    //    need the hasLead field to know if such a message is outstanding)
    // * have accepted some other proposal or
    // * have actually learned a committed result.
    && !v.hasLead
    && v.proposed.None?
    && v.leader.None?
    // Propose that I should lead.
    && msgOps == MessageOps(None, Some(ProposeReqMsg(c.id)))
    // I could record my proposal right now, but I'll just observe
    // my own message.
    && v' == v.(hasLead := true)
  }

  // acceptor decides what to do with the proposal.
  predicate SendProposeAck(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.ProposeReqMsg?
    // Can we accept the proposal?
    && var accept :=
      v.proposed.None? || v.proposed.value==recvMsg.leader;
    // Send the reply
    && msgOps.send == Some(ProposeAckMsg(recvMsg.leader, c.id, accept))
    // Record the acceptance or do nothing
    && v' == if accept then v.(proposed := Some(recvMsg.leader)) else v
  }

  // Leader collects an accept message
  predicate LearnAccept(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.ProposeAckMsg?
    && recvMsg.leader == c.id // reply is to me
    && recvMsg.accept == true  // and it's a positive ack
    && v' == v.(locks := v.locks + {recvMsg.follower})
    && msgOps.send.None?
  }

  // Phase 2

  // This protocol isn't even a little live -- two hosts could propose,
  // accept their own proposal, reject the other's, mutually abort,
  // and have to both give up.
  predicate LearnAndSendAbort(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.ProposeAckMsg?
    && recvMsg.leader == c.id // reply is to me
    && recvMsg.accept == false  // and it's a nak
    && v.proposed == Some(c.id) // and I have actually proposed
    && !recvMsg.accept  // and sender is aborting.
    && msgOps.send == Some(AbortMsg(c.id)) // hasLead stays true, so I'll never try again
  }

  predicate RecvAbort(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.AbortMsg?
    // Only act on messages that are aborting something other than I recorded.
    && v.proposed == Some(recvMsg.leader)
    // Forget the proposal to be open to others.
    && v' == v.(proposed := None)
    && msgOps.send.None?
  }

  predicate SendCommit(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.None?
    && |v.locks| == c.hostCount // Have heard N replies to a proposal I sent
    && v' == v
    && msgOps.send == Some(CommitMsg(c.id))
  }

  predicate RecvCommit(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && msgOps.recv.Some?
    && var recvMsg := msgOps.recv.value;
    && recvMsg.CommitMsg?
    && v' == v.(leader := Some(recvMsg.leader))
    && msgOps.send.None?
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.proposed.None?
    && v.leader.None?
    && !v.hasLead
    && v.locks == {}
  }

  // JayNF
  datatype Step =
    | SendProposeReqStep
    | SendProposeAckStep
    | LearnAcceptStep
    | LearnAndSendAbortStep
    | RecvAbortStep
    | SendCommitStep
    | RecvCommitStep

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
      case SendProposeReqStep => SendProposeReq(c, v, v', msgOps)
      case SendProposeAckStep => SendProposeAck(c, v, v', msgOps)
      case LearnAcceptStep => LearnAccept(c, v, v', msgOps)
      case LearnAndSendAbortStep => LearnAndSendAbort(c, v, v', msgOps)
      case RecvAbortStep => RecvAbort(c, v, v', msgOps)
      case SendCommitStep => SendCommit(c, v, v', msgOps)
      case RecvCommitStep => RecvCommit(c, v, v', msgOps)
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
  import Host
  import Network

  datatype Constants = Constants(hosts: seq<Host.Constants>, network: Network.Constants) {
    predicate WF() {
      // Hosts' local idea of their own ids match their index in our global
      // view.
      && (forall idx | 0<=idx<|hosts| :: hosts[idx].id == idx)
      // Hosts know the number of participants
      && (forall idx | 0<=idx<|hosts| :: hosts[idx].hostCount == |hosts|)
    }
    predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(hosts: seq<Host.Variables>, network: Network.Variables) {
    predicate WF(c: Constants) {
      && |hosts| == |c.hosts|
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && c.WF()
    && v.WF(c)
    && (forall idx:nat | c.ValidHostId(idx) :: Host.Init(c.hosts[idx], v.hosts[idx]))
  }

  // JayNF is pretty simple here since only one transition disjunct at this level.
  datatype Step = Step(idx: HostId, msgOps: MessageOps)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    // only one disjunct, so we don't bother with the 'match' layer.
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && var idx := step.idx;
    && c.ValidHostId(idx)
    && Host.Next(c.hosts[idx], v.hosts[idx], v'.hosts[idx], step.msgOps)
    // all other hosts UNCHANGED
    && (forall otherIdx | c.ValidHostId(otherIdx) && otherIdx != idx :: v'.hosts[idx] == v.hosts[idx])
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

module Proof {
  import opened DistributedSystem

  predicate Safety(c: Constants, v: Variables)
  {
    // If two hosts both conclude there's a leader, they think it's the same leader.
    && (forall hosta, hostb
      |
        && c.ValidHostId(hosta)
        && c.ValidHostId(hostb)
        && v.hosts[hosta].leader.Some?
        && v.hosts[hostb].leader.Some?
      :: v.hosts[hosta].leader == v.hosts[hostb].leader)
  }
  
  predicate Inv(c: Constants, v: Variables)
  {
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
  }

  lemma InvIndunctive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
