//#title DistributedSystem
//#desc DO NOT EDIT THIS FILE! It's a trusted file that specifies how hosts interact
//#desc with one another over the network.

include "host.i.dfy"

// Before we get here, caller must define a type Message that we'll
// use to instantiate network.s.dfy.

module DistributedSystem {
  import opened HostIdentifiers
  import Host
  import Network

  datatype Constants = Constants(
    hosts:seq<Host.Constants>,
    network:Network.Constants) {
    predicate WF() {
      && |hosts| == NumHosts()
      && (forall id | ValidHostId(id) :: hosts[id].WF(id))  // every host knows its id
    }
  }

  datatype Variables = Variables(
    hosts:seq<Host.Variables>,
    network:Network.Variables<Host.Message>) {
    predicate WF(c: Constants) {
      && c.WF()
      && |hosts| == |c.hosts|
    }
  }

  predicate Init(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall id | ValidHostId(id) :: Host.Init(c.hosts[id], v.hosts[id]))
    && Network.Init(c.network, v.network)
  }

  // JayNF
  datatype Step = Step(id:HostId, msgOps: Network.MessageOps<Host.Message>)

  predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
    && v.WF(c)
    && v'.WF(c)
    && ValidHostId(step.id)
    && Host.Next(c.hosts[step.id], v.hosts[step.id], v'.hosts[step.id], step.msgOps)
    && (forall other | ValidHostId(other) && other != step.id :: v'.hosts[other] == v.hosts[other])
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  predicate Next(c:Constants, v:Variables, v':Variables) {
    exists step :: NextStep(c, v, v', step)
  }
}
