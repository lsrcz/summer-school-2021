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
}
