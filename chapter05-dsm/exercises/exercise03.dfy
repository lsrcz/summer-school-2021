//#title Two Phase Commit Safety Proof
//#desc Model a distributed protocol using compound state machines.

// TODO(manos): how should we ensure this file is disseminated at the
// appropriate time, so students aren't waiting for it?
//
// Please begin with a copy of the official solution to exercises 01 & 02,
// to ensure you're not doing battle with mistakes in your own protocol definition.
// The proof is challenging enough for an exercise without fighting protocol bugs.
include "exercise02-solution.dfy"

module Proof {
  import opened Types
  import opened Library
  import opened DistributedSystem
  import opened Obligations

  predicate VoteMessagesAgreeWithParticipantPreferences(c: Constants, v: Variables)
    requires Host.GroupWF(c.hosts, v.hosts)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.VoteMsg?
      && ValidParticipantId(c, msg.sender)
      :: msg.vote == ParticipantConstants(c, msg.sender).preference
    )
  }

  predicate CoordinatorStateSupportedByVote(c: Constants, v: Variables)
    requires Host.GroupWF(c.hosts, v.hosts)
  {
    (forall idx:HostId |
      && ValidParticipantId(c, idx)
      && CoordinatorVars(c, v).votes[idx].Some?
      :: VoteMsg(idx, CoordinatorVars(c, v).votes[idx].value) in v.network.sentMsgs
    )
  }

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
    && VoteMessagesAgreeWithParticipantPreferences(c, v)
    && CoordinatorStateSupportedByVote(c, v)
    && DecisionMsgsAgreeWithDecision(c, v)
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
    // Nobody has agreed with anything yet, so they agree with both.
    assert AllWithDecisionAgreeWithThisOne(c, v, Commit); // witness.
    assert AllWithDecisionAgreeWithThisOne(c, v, Abort); // witness.
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
    // The body of this lemma got really big (expanding foralls, case splits,
    // testing asserts) while I was figuring out what invariants were missing
    // ... and fixing a couple of errors in the protocol definition itself.
    // Afterward, nearly all of that text could be deleted.

    var step :| NextStep(c, v, v', step);   // Witness

    forall msg |
      && msg in v'.network.sentMsgs
      && msg.VoteMsg?
      && ValidParticipantId(c, msg.sender)
      ensures msg.vote == ParticipantConstants(c, msg.sender).preference
    {
      var hostid := step.hostid;
      assert Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], step.msgOps);
    }
    assert VoteMessagesAgreeWithParticipantPreferences(c, v');

    assert Safety(c, v');
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
