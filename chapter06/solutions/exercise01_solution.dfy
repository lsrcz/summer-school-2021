//Your goal is to build a distributed lock server. This challenge differs from
//LockServer in two ways. First, there is no central server that coordinates
//the activity. Second, the hosts can communicate only via asynchronous
//messages; a single state machine transition cannot simultaneously read or
//update the state of two hosts.
//
//To guard against duplicate messages, the nodes associate a monotonically
//increasing epoch number with the lock. Initially, node 0 holds the lock and
//its epoch number is 1. A node that holds the lock can “grant” it to another
//node by sending them a “Grant” message which has an epoch number that is
//greater than the node’s epoch number. A node that receives such a message
//will become the new holder and will set its epoch number to the message’s
//epoch number.  

include "distributed_system.s.dfy"

predicate Safety(s:DistState) {
  && WFState(s)
  && forall i, j :: s.hosts[i].holdsLock && s.hosts[j].holdsLock ==> i == j
}

predicate InFlight(s:DistState, message:Message) {
  && WFState(s)
  && message in s.network.messageSet
  && message.epoch > s.hosts[message.dest].epoch
}

predicate UniqueMessageInFlight(s:DistState) {
  forall m1, m2 :: InFlight(s, m1) && InFlight(s, m2) ==> m1 == m2
}

predicate InFlightPrecludesLockHeld(s:DistState) {
  forall m :: InFlight(s, m) ==> (forall id :: !s.hosts[id].holdsLock)
}

predicate InFlightHasFreshestEpoch(s:DistState) {
  forall m :: InFlight(s, m) ==> (forall id :: s.hosts[id].epoch < m.epoch)
}

predicate LockHolderPrecludesInFlight(s:DistState)
  requires WFState(s)
{
  forall id :: s.hosts[id].holdsLock ==> (forall m :: !InFlight(s, m))
}

predicate LockHolderHasFreshestEpoch(s:DistState)
  requires WFState(s)
{
  forall id :: s.hosts[id].holdsLock ==>
    (forall oid :: oid!=id ==> s.hosts[oid].epoch < s.hosts[id].epoch)
}

predicate Inv(s:DistState) {
  && WFState(s)

  // There are never two messages in flight.
  && UniqueMessageInFlight(s)

  // If a message is flight, no client holds the lock, and
  // the message has the freshest epoch number.
  && InFlightPrecludesLockHeld(s)
  && InFlightHasFreshestEpoch(s)

  // If a clent holds the lock, no message is in flight, and
  // the client has the freshest epoch number.
  && LockHolderPrecludesInFlight(s)
  && LockHolderHasFreshestEpoch(s)

  && Safety(s)
}

lemma SafetyProof()
  ensures forall s :: DistInit(s) ==> Inv(s)
  ensures forall s, s' :: Inv(s) && DistNext(s, s') ==> Inv(s')
  ensures forall s :: Inv(s) ==> Safety(s)
{
  forall s, s' | Inv(s) && DistNext(s, s') ensures Inv(s') {
    var id, a :| NextStep(s, s', id, a);
    if DoAccept(id, s.hosts[id], s'.hosts[id], a) {
      assert UniqueMessageInFlight(s);  // observe
      assert forall m | InFlight(s', m) :: InFlight(s, m);  // observe
      forall m ensures !InFlight(s', m) {
        assert InFlight(s, a.rcv.value);  // observe
        assert !InFlight(s', a.rcv.value);  // observe
      }
      assert Inv(s'); // observe
    } else {
      var recipient :| DoGrant(s.hosts[id], s'.hosts[id], a, recipient); // observe
      assert Inv(s'); // observe
    }
  }
}
