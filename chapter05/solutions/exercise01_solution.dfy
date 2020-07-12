include "../framework.s.dfy"

//////////////////////////////////////////////////////////////////////////////
// Protocol

module Host {
  import opened Base

  datatype Message = Grant(dest:HostId, epoch:int)

  datatype Constants = Constants(id:HostId)
  datatype Variables = Variables(holdsLock:bool, epoch:int)

  predicate DoGrant(k:Constants, s:Variables, s':Variables, a:NetAction<Message>, recipient:HostId) {
    && s.holdsLock == true
    && a.rcv.None?
    && a.send == {Grant(recipient, s.epoch + 1)}
    && s'.holdsLock == false
    && s'.epoch == s.epoch
  }

  predicate DoAccept(k:Constants, s:Variables, s':Variables, a:NetAction<Message>) {
    && a.rcv.Some?
    && a.rcv.value.dest == k.id
    && a.rcv.value.epoch > s.epoch
    && a.send == {}
    && s'.epoch == a.rcv.value.epoch
    && s'.holdsLock == true
  }

  datatype Step = GrantStep(recipient:HostId) | AcceptStep()

  predicate NextStep(k:Constants, s:Variables, s':Variables, a:NetAction<Message>, step:Step) {
    match step {
      case GrantStep(recipient) => DoGrant(k, s, s', a, recipient)
      case AcceptStep() => DoAccept(k, s, s', a)
    }
  }

  predicate Init(k:Constants, s:Variables, id:HostId) {
    && k.id == id
    && s.holdsLock == (id == 0)
    && s.epoch == if id == 0 then 1 else 0
  }
}

module DistributedLock refines DistributedSystem {
  import Host

  type M = Host.Message
  type HConstants = Host.Constants
  type HVariables = Host.Variables
  type HStep(!new,==) = Host.Step

  predicate HInit(k:HConstants, s:HVariables, id:HostId) {
    Host.Init(k, s, id)
  }

  predicate HNextStep(k:HConstants, s:HVariables, s':HVariables, a:NetAction<M>, step:HStep) {
    Host.NextStep(k, s, s', a, step)
  }
}

//////////////////////////////////////////////////////////////////////////////
// Proof

module Proof {
  import opened DistributedLock

  predicate Safety(k:Constants, s:Variables) {
    && WFState(k, s)
    && forall i, j :: s.hosts[i].holdsLock && s.hosts[j].holdsLock ==> i == j
  }

  predicate InFlight(k:Constants, s:Variables, message:M) {
    && WFState(k, s)
    && message in s.network.messageSet
    && message.epoch > s.hosts[message.dest].epoch
  }

  predicate KIsSane(k:Constants) {
    forall id :: id in k.hosts && k.hosts[id].id == id
  }

  predicate Inv(k:Constants, s:Variables) {
    && KIsSane(k)
    && Safety(k, s)
    && (forall m1, m2 :: InFlight(k, s, m1) && InFlight(k, s, m2) ==> m1 == m2)
    && (forall m :: InFlight(k, s, m) ==>
      && (forall id :: !s.hosts[id].holdsLock)
      && (forall id :: s.hosts[id].epoch < m.epoch))
    && (forall id :: s.hosts[id].holdsLock ==>
      && (forall m :: !InFlight(k, s, m))
      && (forall oid :: oid!=id ==> s.hosts[oid].epoch < s.hosts[id].epoch))
  }

  lemma InvInit(k:Constants, s:Variables, s':Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma InvNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires Inv(k, s)
    ensures Inv(k, s')
  {
    var id, a, step :| NextStep(k, s, s', id, a, step);

    if step.AcceptStep? {
      var message := a.rcv.value;
      assert message.epoch > s.hosts[id].epoch;
      assert message.epoch > s.hosts[message.dest].epoch;
      assert forall i :: !s.hosts[i].holdsLock;
      assert (forall id :: s'.hosts[id].holdsLock ==>
        && (forall m :: !InFlight(k, s', m))
        && (forall oid :: oid!=id ==> s'.hosts[oid].epoch < s'.hosts[id].epoch));
    }
  }

  lemma InvImpliesSafety(k:Constants, s:Variables)
    requires Inv(k, s)
    ensures Safety(k, s)
  {
  }
}
