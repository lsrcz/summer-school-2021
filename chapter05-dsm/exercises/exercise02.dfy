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

// Note that we include the result of exercise01. If you have doubts about the
// model you built there, please contact an instructor for a correct solution
// to build on for this exercise.
include "exercise01.dfy"

module Obligations {
  import opened Types
  import opened Library
  import opened DistributedSystem

  // AC-1: All processes that reach a decision reach the same one.
  predicate SafetyAC1(c: Constants, v: Variables)
    requires Host.GroupWF(c.hosts, v.hosts)
  {
    // All hosts that reach a decision reach the same one
    false // Replace me
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  // AC-3: The Commit decision can only be reached if all processes prefer Yes.
  predicate SafetyAC3(c: Constants, v: Variables)
    requires Host.GroupWF(c.hosts, v.hosts)
  {
    false // Replace me
  }

  // AC-4: If all processes prefer Yes, then the decision must be Commit.
  predicate SafetyAC4(c: Constants, v: Variables)
    requires Host.GroupWF(c.hosts, v.hosts)
  {
    false // Replace me
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  //#instructor Player 1
  predicate Safety(c: Constants, v: Variables)
    requires Host.GroupWF(c.hosts, v.hosts)
  {
    && SafetyAC1(c, v)
    && SafetyAC3(c, v)
    && SafetyAC4(c, v)
  }
}
