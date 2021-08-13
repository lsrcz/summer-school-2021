//#title 
//#desc TODO split into multiple steps:
// 02 define the spec of atomic commit
// 03 prove AC1,3,4 on spec
// 04 then (given a correct spec) port forward the chapter5 implementation of 2PC to here
// 05 then proving refinement
//#desc TODO becomes exercise02-03-04

/*
 * This file defines the specification of atomic commit in the form of a state
 * machine. Then we add proofs of three of the five properties by which AC is
 * often informally defined.
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
 */

module Types {
  type ParticipantId = nat

  datatype Vote = Yes | No
  datatype Decision = Commit | Abort

  // Have to define our message datatype so network can refer to it.
  // (There are cleverer ways to parameterize the network module, but
  // we're trying to avoid getting fancy with the Dafny module system.)
  datatype Message =
    | VoteReqMsg                           // from leader
    | VoteMsg(sender: ParticipantId, vote: Vote)  // from participant
    | DecisionMsg(decision: Decision)
}

// This is the specification state machine. It defines what the implementation
// is trying to accomplish, while ignoring all implementation details.
module AtomicCommit {
  import opened Types
  import opened Library

  datatype Constants = Constants(participantCount: nat, preferences:seq<Vote>)
  {
    predicate WF() {
      && |preferences| == participantCount
    }
    predicate ValidParticipant(idx: ParticipantId) { idx < participantCount }

  }
  datatype Variables = Variables(coordinatorDecision: Option<Decision>, 
                                 participantDecisions: seq<Option<Decision>>)
  {
    predicate WF(c: Constants) {
      && |participantDecisions| == c.participantCount
    }
  }
  
  function UltimateDecision(c: Constants) : Decision
    requires c.WF()
  {
    if (forall idx:ParticipantId | idx < c.participantCount :: c.preferences[idx] == Yes) then Commit else Abort
  }

  predicate Init(c: Constants, v: Variables) 
  {
    && c.WF()
    && v.WF(c)
    && (forall idx:ParticipantId | idx < c.participantCount :: v.participantDecisions[idx].None?)
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

// To increase our confidence that we understand the specification state machine,
// we can state (and prove) some properties about it.
// We don't state AC2 because it's a history property, not stateable as a
// single-state safety property. But it should be clearly evident from the
// state machine structure.
// We don't state AC5 because it's a liveness property, which is out of scope
// for this course.
module AtomicCommitProperties {
  import opened AtomicCommit

  predicate SafetyAC1(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    // All hosts that reach a decision reach the same one
    || AllWithDecisionAgreeWithThisOne(c, v, Commit)
    || AllWithDecisionAgreeWithThisOne(c, v, Abort)
  }

  // AC2 is sort of a history predicate; we're going to ignore it.

  predicate SafetyAC3(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    && (exists idx:ParticipantId
      :: c.ValidParticipantId(idx) && c.participants[idx].preference.No?)
      ==> AllWithDecisionAgreeWithThisOne(c, v, Abort)
  }

  predicate SafetyAC4(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
    && (forall idx:ParticipantId
        | c.ValidParticipantId(idx) :: c.participants[idx].preference.Yes?)
      ==> AllWithDecisionAgreeWithThisOne(c, v, Commit)
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

  lemma SafetyInit(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Safety(c, v)
  {
  }

    //requires Inv(c, v)  I think the invariant for the spec is trivial, which is a good thing for a spec!
  lemma SafetyNext(c: Constants, v: Variables, v': Variables)
    requires Safety(c, v'
    requires Next(c, v, v')
    ensures Safety(c, v')
  {
  }
}

