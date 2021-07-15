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
//greater than the node's epoch number. A node that receives such a message
//will become the new holder and will set its epoch number to the message’v
//epoch number.  

include "distributed_system.s.dfy"

predicate Safety(v:DistState) {
  && WFState(v)
  && forall i, j :: v.hosts[i].holdsLock && v.hosts[j].holdsLock ==> i == j
}

predicate InFlight(v:DistState, message:Message) {
  && WFState(v)
  && message in v.network.messagesEverSent
  && message.epoch > v.hosts[message.dest].epoch
}

predicate UniqueMessageInFlight(v:DistState) {
  forall m1, m2 :: InFlight(v, m1) && InFlight(v, m2) ==> m1 == m2
}

predicate InFlightPrecludesLockHeld(v:DistState) {
  forall m :: InFlight(v, m) ==> (forall id :: !v.hosts[id].holdsLock)
}

predicate InFlightHasFreshestEpoch(v:DistState) {
  forall m :: InFlight(v, m) ==> (forall id :: v.hosts[id].epoch < m.epoch)
}

predicate LockHolderPrecludesInFlight(v:DistState)
  requires WFState(v)
{
  forall id :: v.hosts[id].holdsLock ==> (forall m :: !InFlight(v, m))
}

predicate LockHolderHasFreshestEpoch(v:DistState)
  requires WFState(v)
{
  forall id :: v.hosts[id].holdsLock ==>
    (forall oid :: oid!=id ==> v.hosts[oid].epoch < v.hosts[id].epoch)
}

predicate Inv(v:DistState) {
  && WFState(v)

  // There are never two messages in flight.
  && UniqueMessageInFlight(v)

  // If a message is flight, no client holds the lock, and
  // the message has the freshest epoch number.
  && InFlightPrecludesLockHeld(v)
  && InFlightHasFreshestEpoch(v)

  // If a clent holds the lock, no message is in flight, and
  // the client has the freshest epoch number.
  && LockHolderPrecludesInFlight(v)
  && LockHolderHasFreshestEpoch(v)

  && Safety(v)
}

lemma SafetyProof()
  ensures forall v :: DistInit(v) ==> Inv(v)
  ensures forall v, v' :: Inv(v) && DistNext(v, v') ==> Inv(v')
  ensures forall v :: Inv(v) ==> Safety(v)
{
  forall v, v' | Inv(v) && DistNext(v, v') ensures Inv(v') {
    var id, a :| NextStep(v, v', id, a);
    if DoAccept(id, v.hosts[id], v'.hosts[id], a) {
      assert UniqueMessageInFlight(v);  // observe
      assert forall m | InFlight(v', m) :: InFlight(v, m);  // observe
      forall m ensures !InFlight(v', m) {
        assert InFlight(v, a.rcv.value);  // observe
        assert !InFlight(v', a.rcv.value);  // observe
      }
      assert Inv(v'); // observe
    } else {
      var recipient :| DoGrant(v.hosts[id], v'.hosts[id], a, recipient); // observe
      assert Inv(v'); // observe
    }
  }
}
