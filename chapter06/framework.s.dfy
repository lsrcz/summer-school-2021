//////////////////////////////////////////////////////////////////////////////
// Environment spec

module Base {
  function NumHosts() : nat
    ensures NumHosts() > 0

  newtype HostId = b: int | 0 <= b < NumHosts()
  function AllHosts() : set<HostId> {
    set h:HostId | true
  }
  datatype Option<V> = None | Some(value:V)
  datatype NetAction<M> = NetAction(rcv:Option<M>, send:set<M>)
}

module Network {
  import opened Base

  datatype Constants = Constants()
  datatype Variables<M> = Variables(messageSet:set<M>)

  predicate Init(k:Constants, s:Variables) {
    s.messageSet == {}
  }

  predicate Next(k:Constants, s:Variables, s':Variables, a:NetAction) {
    && (a.rcv.Some? ==> a.rcv.value in s.messageSet)
    && s'.messageSet == s.messageSet + a.send
  }
}

abstract module DistributedSystem {
  import opened Base
  import Network

  // parameters filled in by refining module
  type M(!new,==)
  type HConstants
  type HVariables
  type HStep(!new,==)
  predicate HInit(k:HConstants, s:HVariables, id:HostId)
  predicate HNextStep(k:HConstants, s:HVariables, s':HVariables, a:NetAction<M>, step:HStep)

  datatype Constants
    = Constants(hosts:map<HostId, HConstants>, network:Network.Constants)
  datatype Variables
    = Variables(hosts:map<HostId, HVariables>, network:Network.Variables<M>)
  
  predicate WFState(k:Constants, s:Variables) {
    && k.hosts.Keys == AllHosts()
    && s.hosts.Keys == AllHosts()
  }

  predicate Init(k:Constants, s:Variables) {
    && WFState(k, s)
    && (forall id :: HInit(k.hosts[id], s.hosts[id], id))
    && Network.Init(k.network, s.network)
  }

  predicate NextStep(k:Constants, s:Variables, s':Variables, id:HostId, a:NetAction<M>, step:HStep) {
    && WFState(k, s)
    && WFState(k, s')
    && HNextStep(k.hosts[id], s.hosts[id], s'.hosts[id], a, step)
    && (forall other :: other != id ==> s'.hosts[other] == s.hosts[other])
    && Network.Next(k.network, s.network, s'.network, a)
  }

  predicate Next(k:Constants, s:Variables, s':Variables) {
    exists id, a, step :: NextStep(k, s, s', id, a, step)
  }
}


