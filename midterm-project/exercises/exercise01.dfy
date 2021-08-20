//#title Midterm Project
//#desc Build a distributed lock server.

// This challenge differs from LockServer in two ways. First, there is no
// central server that coordinates the activity. Second, the hosts can
// communicate only via asynchronous messages; a single state machine
// transition cannot simultaneously read or update the state of two hosts.
//
// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1. A node that holds the lock can “grant” it to another
// node by sending them a “Grant” message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’v
// epoch number.

// You'll first need to modify 'protocol.i.dfy' to define the protocol message
// format and the host behavior.
// Then come back here define the safety condition and prove that the
// distributed system made from that protocol maintains it.

include "distributed_system.s.dfy"

// the lock simulatneously.
predicate Safety(v:DistVars) {
  false // Replace this placeholder with an appropriate safety condition: no two clients hold
}

// TODO XXX should we give some signatures below as hints?

predicate Inv(v:DistVars) {
  true // Replace this placeholder with an invariant that's inductive and supports Safety.
}

lemma SafetyProof()
  ensures forall v :: DistInit(v) ==> Inv(v)
  ensures forall v, v' :: Inv(v) && DistNext(v, v') ==> Inv(v')
  ensures forall v :: Inv(v) ==> Safety(v)
{
}
