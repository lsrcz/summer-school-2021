//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (exercise01) accomplishes the Safety spec (exercise02)

// TODO(manos): how should we ensure this file is disseminated at the
// appropriate time, so students aren't waiting for it?

include "model_for_ex03.dfy"

module Proof {
  import opened Types
  import opened Library
  import opened DistributedSystem
  import opened Obligations

  predicate DecisionMsgsAgreeWithDecision(c: Constants, v: Variables)
    requires Host.GroupWF(c.hosts, v.hosts)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.DecisionMsg?
      :: CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v), msg.decision)
    )
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && Host.GroupWF(c.hosts, v.hosts)
    // We'll give you one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(c, v)
    // ...but you'll need more.
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
