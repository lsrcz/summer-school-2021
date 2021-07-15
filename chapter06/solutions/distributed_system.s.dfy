//////////////////////////////////////////////////////////////////////////////
// DistributedSystem
//////////////////////////////////////////////////////////////////////////////

// DO NOT EDIT THIS FILE! It's a trusted file that specifies how hosts interact
// with one another over the network.

include "protocol.i.dfy"

// Before we get here, caller must define a type Message that we'll
// use to instantiate network.s.dfy.

datatype DistState = DistState(
  hosts:map<HostId, HostState>, network:NetState<Message>)

predicate WFState(v:DistState) {
  // We don't lose track of any of the hosts.
  && v.hosts.Keys == AllHosts()
}

predicate DistInit(v:DistState) {
  && WFState(v)
  && (forall id :: HostInit(v.hosts[id], id))
  && NetInit(v.network)
}

predicate NextStep(v:DistState, v':DistState, id:HostId, a:NetAction<Message>) {
  && WFState(v)
  && WFState(v')
  && HostNext(id, v.hosts[id], v'.hosts[id], a)
  && (forall other :: other != id ==> v'.hosts[other] == v.hosts[other])
  && NetNext(v.network, v'.network, a)
}

predicate DistNext(v:DistState, v':DistState) {
  exists id, a :: NextStep(v, v', id, a)
}
