/*
 * Single-instance 2PC.
 */

include "../../library/library.dfy"

module Types {
  type HostId = nat
}

module Host {
  import opened Types

  datatype Constants = Constants(id: HostId, hostCount: nat)
  datatype Variables = Variables(
    // Follower state
    proposed: Option<HostId>, // a proposed value locked at this host
    leader: Option<HostId>,   // a committed result

    // Leader state
    hasLead: bool,           // I only ever get to propose once
    locks: set<HostId>        // who has acked my proposal
    )


  datatype Message =
    | ProposeReqMsg(leader: nat)   // from leader
    | ProposeAckMsg(leader:nat, follower: nat, accept: bool) // from follower
    | AbortMsg(leader: nat)        // from leader
    | CommitMsg(leader: nat)       // from leader
  
  predicate SendProposeReq(c: Constants, v: Variables, v': Variables)
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
    && sendMessages == { ProposeReqMsg(c.id) }
    // I could record my proposal right now, but I'll just observe
    // my own message.
    && v' == v.(proposed := true)
  }

  // acceptor decides what to do with the proposal.
  predicate SendProposeAck(c: Constants, v: Variables, v': Variables)
  {
    && recvMessage.Some?
    && recvMessage.ProposeReqMsg?
    // Can we accept the proposal?
    && var accept :=
      v.proposed.None? || v.proposed.value==recvMessage.value.leader;
    // Send the reply
    && sendMessages == { ProposeAckMsg(recvMessage.value.leader, c.id, accept) }
    // Record the acceptance or do nothing
    && v' == if accept then v.(proposed := recvMessage.value.leader) else v
  }

  // Leader collects an accept message
  predicate LearnAccept(c: Constants, v: Variables, v': Variables)
  {
    && recvMessage.Some?
    && recvMessage.value.ProposeAckMsg?
    && recvMessage.value.leader == c.id // reply is to me
    && recvMessage.value.accept == true  // and it's a positive ack
    && v' == v.(locks := v.locks + {recvMessage.value.follower})
    && sendMessages == {}
  }

  // Phase 2

  // This protocol isn't even a little live -- two hosts could propose,
  // accept their own proposal, reject the other's, mutually abort,
  // and have to both give up.
  predicate SendAbort(c: Constants, v: Variables, v': Variables)
  {
    && recvMessage.Some?
    && recvMessage.value.ProposeAck?
    && recvMessage.value.leader == c.id // reply is to me
    && recvMessage.value.accept == false  // and it's a nak
    && v.proposed == Some(c.id) // and I have actually proposed
    && !recvMessage.value.accept  // and sender is aborting.
    && sendMessages == { AbortMsg(c.id) }  // hasLead stays true, so I've lost
  }

  predicate RecvAbort(c: Constants, v: Variables, v': Variables)
  {
    && recvMessage.Some?
    && recvMessage.value.AbortMsg?
    && sendMessages == { }
    // Can ignore messages that are aborting something other than I recorded.
    && v.proposed == Some(recvMessage.value.leader)
    // Forget the proposal to be open to others.
    && v' == v.(proposed := None)
    && sendMessages == { }
  }

  predicate SendCommit(c: Constants, v: Variables, v': Variables)
  {
    && recvMessage.None?
    && |v.locks| == c.hostCount // Have heard N replies to a proposal I sent
    && sendMessages == { CommitMsg(c.id) }
    && v' == v
  }

  predicate RecvCommit(c: Constants, v: Variables, v': Variables)
  {
    && recvMessage.Some?
    && recvMessage.value.CommitMsg?
    && sendMessages == { }
    && v' == v.(leader := recvMessage.value.leader)
  }
}
