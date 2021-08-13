//#title The trusted environment model
//#desc for building distributed systems protocols.
//#desc Defines assumptions about the network, and then defines how the
//#desc distributed system hosts (defined by the protocol) interact with the
//#desc network.

// TODO(jonh): Explain abstract module rules

include "library.dfy"

module DistributedSystemTypes {
  // Both the protocol and the DistributedSystem need to identify hosts by HostId
  type HostId = nat
}

abstract module HostIfc {
  import opened Library

  type Constants
  type Variables
  type Message(==) // Obligation to be supplied by refining implementation.

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)

  predicate Init(c: Constants, v: Variables)
    // Obligation to be supplied by refining implementation.

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    // Obligation to be supplied by refining implementation.
}

abstract module Network {
  import HI : HostIfc

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<HI.Message>)

  predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  predicate Next(c: Constants, v: Variables, v': Variables, msgOps: HI.MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}

abstract module DistributedSystem {
  import opened DistributedSystemTypes
  import Network
  import HI = Network.HI

  datatype Constants = Constants(
    hosts: seq<HI.Constants>,
    network: Network.Constants)
  {
    predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
  }

  datatype Variables = Variables(
    hosts: seq<HI.Variables>,
    network: Network.Variables)
  {
    predicate WF(c: Constants) {
      && |hosts| == |c.hosts|
    }
  }

  predicate ProtocolHostsInit(c: Constants, v: Variables)
    // Obligation to be supplied by refining implementation.
    // This interface gives the specific protocol an opportunity to
    // set up constraints across the various hosts.

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && ProtocolHostsInit(c, v)
    && Network.Init(c.network, v.network)
  }

  predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: HI.MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && HI.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: HI.MessageOps)

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
