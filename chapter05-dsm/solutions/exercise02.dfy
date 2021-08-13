//#title Two Phase Commit Safety Specification Predicate
//#desc Express the English Atomic Commit safety properties as predicates
//#desc over the compound state machine model from exercise01.

/*
 * 2PC should satisfy the Atomic Commit specification. English design doc:
 *
 * AC-1: All processes that reach a decision reach the same one.
 * AC-3: The Commit decision can only be reached if all processes prefer Yes.
 * AC-4: If all processes prefer Yes, then the decision must be Commit.
 *
 * Note that the full Atomic Commit spec includes these additional properties,
 * but you should ignore them for this exercise:
 * AC-2: (stability) A process cannot reverse its decision after it has reached one.
 *       (best modeled with refinement)
 * AC-5: (liveness) All processes eventually decide.
 *
 */

include "exercise01.dfy"

module Obligations {
  import opened Types
  import opened Library
  import opened TwoPCDistributedSystem

//#start-elide
  predicate AllWithDecisionAgreeWithThisOne(c: Constants, v: Variables, decision: Decision)
    requires c.WF()
    requires v.WF(c)
    // I pulled this conjunction into a named predicate because Dafny warned of
    // no trigger for the exists.
  {
    && (v.coordinator.decision.Some? ==> v.coordinator.decision.value == decision)
    && (forall idx:ParticipantId
      | c.ValidParticipantId(idx) && v.participants[idx].decision.Some?
      :: v.participants[idx].decision.value == decision)
  }

//#end-elide
  // AC-1: All processes that reach a decision reach the same one.
  predicate SafetyAC1(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    // All hosts that reach a decision reach the same one
//#exercise    true
//#start-elide
    || AllWithDecisionAgreeWithThisOne(c, v, Commit)
    || AllWithDecisionAgreeWithThisOne(c, v, Abort)
//#end-elide
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  predicate SafetyAC3(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
//#exercise    true
//#start-elide
    && (exists idx:ParticipantId
      :: c.ValidParticipantId(idx) && c.participants[idx].preference.No?)
      ==> AllWithDecisionAgreeWithThisOne(c, v, Abort)
//#end-elide
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  predicate SafetyAC4(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
//#exercise    true
//#start-elide
    && (forall idx:ParticipantId
        | c.ValidParticipantId(idx) :: c.participants[idx].preference.Yes?)
      ==> AllWithDecisionAgreeWithThisOne(c, v, Commit)
//#end-elide
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  //#instructor Player 1
  predicate Safety(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    && SafetyAC1(c, v)
    && SafetyAC3(c, v)
    && SafetyAC4(c, v)
  }
}
