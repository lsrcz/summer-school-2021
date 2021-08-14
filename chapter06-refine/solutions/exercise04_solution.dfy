//#title Refinement proof for 2PC
//#desc Show that Two Phase Commit refines the Atomic Commit sate machine spec.

// This proof shouldn't be terribly brutal, since you have a roadmap for the
// relevant invariants from chapter05. You can discard the AC properties (since
// those are proven about the spec in exercise03, and therefore about any state
// machine that refines the spec).

include "spec_model_for_ex04.dfy"
include "impl_model_for_ex04.dfy"

// This Dafny "abstract module" establishes the proof obligations for the refinement:
// you must fill in the function and lemma bodies in a module that `refines` this one.
// So leave this module as-is, and fill in the bodies in the refining module.
// (This structure isn't necessary, but it's a nice way to separate the statement
// of the theorem from its proof.)
abstract module RefinementTheorem {
  import opened CommitTypes
  import opened Types
  import opened Library
  import opened DistributedSystem
  import opened TwoPCInvariantProof
  import AtomicCommit

  function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants
    requires c.WF()

  function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables
    requires v.WF(c)

  predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    requires DistributedSystem.Init(c, v)
    ensures Inv(c, v)
    ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables)
    requires DistributedSystem.Next(c, v, v')
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v')

}

module RefinementProof refines RefinementTheorem {
  // No imports needed because we inherited them from the abstract module RefinementTheorem
  import opened Obligations
  import opened CoordinatorHost

  // Here's a handy function to save you some typing.
  function ParticipantCount(c: DistributedSystem.Constants) : nat
    requires c.WF()
  {
    CoordinatorConstants(c).participantCount
  }

  // The main challenge of setting up a refinement: abstracting from the
  // low-level (protocol) state to the high-level (spec) state.
  function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants
  {
//#exercise    AtomicCommit.Constants(0, [])   // Replace me
//#start-elide
    AtomicCommit.Constants(ParticipantCount(c),
      seq(ParticipantCount(c), idx requires 0 <= idx < ParticipantCount(c) => ParticipantConstants(c, idx).preference))
//#end-elide
  }

  function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables
  {
//#exercise    AtomicCommit.Variables(None, [])   // Replace me
//#start-elide
    AtomicCommit.Variables(CoordinatorVars(c, v).decision,
      seq(ParticipantCount(c), idx requires 0 <= idx < ParticipantCount(c) => ParticipantVars(c, v, idx).decision))
//#end-elide
  }

  predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
  {
    // Just point at the invariant from the chapter05 proof (in impl_model).
//#exercise    false  // Replace me
//#start-elide
    TwoPCInvariantProof.Inv(c, v)
//#end-elide
  }

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    /*
    requires DistributedSystem.Init(c, v)
    ensures Inv(c, v)
    ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))*/
  {
  }

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables)
    /*requires DistributedSystem.Next(c, v, v')
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v')*/
  {
    // Advice: appeal to the existing proof to get Inv(c, v')!
//#start-elide
    InvInductive(c, v, v'); // Reuse this from chapter05/exercises/exercise03 proof
//#end-elide

    // The "new" part of this proof is to explain which AtomicCommit
    // (spec-level) action happened in response to each 2PC (protocol-level)
    // action. So the general strategy is: use skolemization (var :|) to "learn"
    // which thing happened in the DistributedSystem, split the cases, and
    // assert the right AtomicCommit.NextStep() predicate. Mostly, Dafny needs
    // those asserts because they're witnesses to the `exists` in AtomicCommit.Next().
//#start-elide
    // Skolemize the DistributedSystem step (learn which step we need to
    // consider), and case split on type of the host that stepped (Coordinator
    // or Participant).
    var step :| DistributedSystem.NextStep(c, v, v', step);
    var hc := c.hosts[step.hostid];

    // Dafny needed some help connecting the abstract view of the constants with the
    // DistributedSystem view.
    assert forall idx:HostId | ConstantsAbstraction(c).ValidParticipant(idx)
      :: ConstantsAbstraction(c).preferences[idx] == ParticipantConstants(c, idx).preference;

    match hc {
      case CoordinatorConstants(_) => {
        // Skolemize the CoordinatorHost step that happened, and case split on it.
        var coordStep :| CoordinatorHost.NextStep(CoordinatorConstants(c), CoordinatorVars(c, v), CoordinatorVars(c, v'), coordStep, step.msgOps);
        match coordStep {
          // These two cases are noops
          case SendReqStep => { assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v'); }
          case LearnVoteStep => { assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v'); }
          case DecideStep(decision) => {
            if CoordinatorVars(c, v).decision.None? {
              // Coordinator recored a new decision; provide a witness to that step in the AtomicCommit machine
              assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.CoordinatorLearnsStep); // witness to the exists
            }
          }
        }
      }
      case ParticipantConstants(_) => {
        // Skolemize the ParticipantHost step that happened, and case split on it.
        var idx := step.hostid;
        var partStep :| ParticipantHost.NextStep(ParticipantConstants(c, idx), ParticipantVars(c, v, idx), ParticipantVars(c, v', idx), partStep, step.msgOps);
        match partStep {
          case VoteStep => {
            if ParticipantConstants(c, idx).preference.No? && ParticipantVars(c, v, idx).decision.None? {
              // Participant recorded an Abort decision
              assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.ParticipantLearnsStep(idx)); // witness to the exists
            }
          }
          case LearnDecisionStep => {
            if ParticipantVars(c, v, idx).decision.None? {
              // Participant recorded a decision sent from the coordinator.
              assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.ParticipantLearnsStep(idx)); // witness to the exists
//              assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
            }
          }
        }
      }
    }
//#end-elide
  }
}
