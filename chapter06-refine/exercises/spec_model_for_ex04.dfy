//#desc Specification state machine for refinement proof in exercise04.

// This file is an instructor-provided solution to the Atomic Commit spec in
// exercise02, so you're not doing battle with a spec that's impossible to
// satisfy -- or getting away with refining to a spec that's trivial.

/*
 * Define the specification of atomic commit in the form of a state
 * machine.
 *
 * The abstract model doesn't worry about network communication. Instead,
 * it models the input:
 *     - which participants prefer which outcomes
 * and the outputs:
 *     - what the coordinator thinks the decision was
 *     - what each participant thinks the decision was
 * This definition should make it obvious by inspection that the output decisions
 * all agree (AC1) and they output decisions comply with the input preferences
 * (AC3, AC4).
 *
 * In a future exercise, we'll show refinement: that the 2PC protocol correctly
 * computs
 *
 * Note that this is a (trusted) spec -- this file already passes Dafny, but
 * it's a terrible spec, because it doesn't say anything useful. (Recall the
 * lesson of chapter01/exercise20.dfy.) Consider running your result past an
 * instructor in office hours to be sure it's a good spec.
 */

include "../../library/Library.dfy"
module CommitTypes {
  // How a particular participant feels.
  datatype Vote = Yes | No
  // What decision has been reached by the protocol.
  datatype Decision = Commit | Abort
}


// This is the specification state machine. It defines what the implementation
// is trying to accomplish, while ignoring all implementation details.
module AtomicCommit {
  import opened CommitTypes
  import opened Library

  type ParticipantId = nat

  // We'll give you the state data structure; it'll be your job to define the
  // actions.  The input preferences are constant, so we record them here.
  datatype Constants = Constants(participantCount: nat, preferences:seq<Vote>)
  {
    predicate WF() {
      && |preferences| == participantCount
    }
    predicate ValidParticipant(idx: ParticipantId) { idx < participantCount }

  }

  // The outputs are the decision reached by the coordinator and those
  // observed by the participants.
  // None? capture the idea that initially nobody knows the decision.
  // In your actions, make AC2 abundantly obvious: once a None? turns into a
  // Some?, it can't ever change.
  datatype Variables = Variables(coordinatorDecision: Option<Decision>,
                                 participantDecisions: seq<Option<Decision>>)
  {
    predicate WF(c: Constants) {
      && |participantDecisions| == c.participantCount
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && c.WF()
    && v.WF(c)
    && v.coordinatorDecision.None?
    && (forall idx:ParticipantId | c.ValidParticipant(idx) :: v.participantDecisions[idx].None?)
  }

  // We can tell what the ultimate decision has to be just from the constants.
  // Define that in this function, and then use it to constrain what actions
  // can happen in the state machine.
  function UltimateDecision(c: Constants) : Decision
    requires c.WF()
  {
    if (forall idx:ParticipantId | c.ValidParticipant(idx) :: c.preferences[idx] == Yes) then Commit else Abort
  }

  predicate ParticipantLearnsDecision(c: Constants, v: Variables, v': Variables, idx: ParticipantId)
  {
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && c.ValidParticipant(idx)
    && v.participantDecisions[idx].None?  // enforces one-time decision property
    && v' == v.(participantDecisions := v.participantDecisions[idx := Some(UltimateDecision(c))])
  }

  predicate CoordinatorLearnsDecision(c: Constants, v: Variables, v': Variables)
  {
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && v.coordinatorDecision.None?  // enforces one-time decision property
    && v' == v.(coordinatorDecision := Some(UltimateDecision(c)))
  }

  // JayNF
  datatype Step =
    | ParticipantLearnsStep(idx:ParticipantId)
    | CoordinatorLearnsStep()

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && c.WF()
    && v.WF(c)
    && v'.WF(c)
    && (
      match step
        case ParticipantLearnsStep(idx) => ParticipantLearnsDecision(c, v, v', idx)
        case CoordinatorLearnsStep() => CoordinatorLearnsDecision(c, v, v')
      )
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}
