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

  function ParticipantCount(c: DistributedSystem.Constants) : nat
    requires c.WF()
  {
    CoordinatorConstants(c).participantCount
  }

  function ConstantsAbstraction(c: DistributedSystem.Constants) : AtomicCommit.Constants
  {
    AtomicCommit.Constants(ParticipantCount(c),
      seq(ParticipantCount(c), idx requires 0 <= idx < ParticipantCount(c) => ParticipantConstants(c, idx).preference))
  }

  function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : AtomicCommit.Variables
  {
    AtomicCommit.Variables(CoordinatorVars(c, v).decision,
      seq(ParticipantCount(c), idx requires 0 <= idx < ParticipantCount(c) => ParticipantVars(c, v, idx).decision))
  }

/*
  predicate VoteMessagesAgreeWithParticipantPreferences(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    requires v.WF(c)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.VoteMsg?
      && ValidParticipantId(c, msg.sender)
      :: msg.vote == ParticipantConstants(c, msg.sender).preference
    )
  }

  predicate CoordinatorStateSupportedByVote(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    requires c.WF()
    requires v.WF(c)
  {
    (forall idx:ParticipantId |
      && c.ValidParticipantId(idx)
      && v.coordinator.votes[idx].Some?
      :: VoteMsg(idx, v.coordinator.votes[idx].value) in v.network.sentMsgs
    )
  }

  predicate DecisionMsgsAgreeWithDecision(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    requires c.WF()
    requires v.WF(c)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.DecisionMsg?
      :: CoordinatorHost.ObservesResult(c.coordinator, v.coordinator, msg.decision)
    )
  }
*/

  predicate Inv(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
  {
  /*
    && c.WF()
    && v.WF(c)
    && VoteMessagesAgreeWithParticipantPreferences(c, v)
    && CoordinatorStateSupportedByVote(c, v)
    && DecisionMsgsAgreeWithDecision(c, v)
    */
    && TwoPCInvariantProof.Inv(c, v)
  }

  lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
    /*
    requires DistributedSystem.Init(c, v)
    ensures Inv(c, v)
    ensures AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))*/
  {
    assert Inv(c, v);
    assert AtomicCommit.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v));
  }

  lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables)
    /*requires DistributedSystem.Next(c, v, v')
    requires Inv(c, v)
    ensures Inv(c, v')
    ensures AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v')*/
  {
    assert Inv(c, v);
    assert DistributedSystem.Next(c, v, v');
    InvInductive(c, v, v'); // Reuse this from chapter05/exercises/exercise03 proof
    assert Inv(c, v');

    // Skolemize the DistributedSystem step (learn which step we need to
    // consider), and case split on type of the host that stepped (Coordinator
    // or Participant).
    var step :| DistributedSystem.NextStep(c, v, v', step);
    var hc := c.hosts[step.hostid];
    match hc {
      case CoordinatorConstants(_) => {
        // Skolemize the CoordinatorHost step that happened, and case split on it.
        var hstep :| CoordinatorHost.NextStep(CoordinatorConstants(c), CoordinatorVars(c, v), CoordinatorVars(c, v'), hstep, step.msgOps);
        match hstep {
          case SendReqStep => {
            assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
          }
          case LearnVoteStep => {
            assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
          }
          case DecideStep(decision) => {
            if CoordinatorVars(c, v).decision.Some? {
              // If coordinator had already decided, then this step is (had better be) a noop, because
              // we didn't change the decision.
              assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
            } else {
              // Coordinator made a decision; provide a witness to that step in the AtomicCommit machine
              assert CoordinatorVars(c, v).WF(CoordinatorConstants(c));
              assert |v.hosts|-1 == CoordinatorConstants(c).participantCount;
              assert |CoordinatorVars(c, v).votes| == |v.hosts|-1;
              assert forall hostIdx:HostId | hostIdx < ParticipantCount(c) :: CoordinatorVars(c, v').votes[hostIdx].value
                == ParticipantConstants(c, hostIdx).preference;
              if (forall hostIdx:HostId | hostIdx < ParticipantCount(c) :: CoordinatorVars(c, v').votes[hostIdx].value.Yes?) {
                assert CoordinatorVars(c, v').decision.value.Commit?;
              } else {
                assert CoordinatorVars(c, v').decision.value.Abort?;
              }
              assert ConstantsAbstraction(c).participantCount == ParticipantCount(c);
              assert forall idx:HostId :: ConstantsAbstraction(c).ValidParticipant(idx) == (idx < ParticipantCount(c));
              if (forall hostIdx:HostId | hostIdx < ParticipantCount(c) :: ParticipantConstants(c, hostIdx).preference.Yes?) {
                assert AtomicCommit.UltimateDecision(ConstantsAbstraction(c)).Commit?;
              } else {
                assert AtomicCommit.UltimateDecision(ConstantsAbstraction(c)).Abort?;
              }
              assert CoordinatorVars(c, v').decision.value == AtomicCommit.UltimateDecision(ConstantsAbstraction(c));
              assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.CoordinatorLearnsStep);
              assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
            }
          }
        }
        assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
      }
      case ParticipantConstants(_) => {
        assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
      }
    }
    assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v');

//    assert forall idx:AtomicCommit.ParticipantId :: ConstantsAbstraction(c).ValidParticipant(idx) == ValidParticipantId(c, idx); 
//
//    var step :| DistributedSystem.NextStep(c, v, v', step);
//    var hc := c.hosts[step.hostid];
//    match hc {
//      case CoordinatorConstants => {
//        assert DecisionMsgsAgreeWithDecision(c, v'); // Trigger
//        //if VariablesAbstraction(c, v) == VariablesAbstraction(c, v') {
//        assert Coordinator(c, v, v', msgOps);
//        assert CoordinatorHost.Next(c.coordinator, v.coordinator, v'.coordinator, msgOps);
//        assert (forall idx:nat | c.ValidParticipantId(idx) :: v'.participants[idx] == v.participants[idx]);
//
//        //assert exists step2 :: CoordinatorHost.NextStep(c.coordinator, v.coordinator, v'.coordinator, step2, msgOps);
//        var coordinatorStep :| CoordinatorHost.NextStep(c.coordinator, v.coordinator, v'.coordinator, coordinatorStep, msgOps);
//        match coordinatorStep {
//          case SendReqStep() => {
//            assert SendReq(c.coordinator, v.coordinator, v'.coordinator, msgOps);
//            assert v.coordinator == v'.coordinator;
//            assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
//            //assert v == v';
//            //assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
//          }
//          case LearnVoteStep() => {
//            assert LearnVote(c.coordinator, v.coordinator, v'.coordinator, msgOps);
//            assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
//            //assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
//          }
//          case DecideStep(decision) => {
//            assert Decide(c.coordinator, v.coordinator, v'.coordinator, decision, msgOps);
//            if(v.coordinator.decision.None?) {
//              //assume false;
//              assert v'.coordinator.decision.Some?;
//              var decision := v'.coordinator.decision.value;
//              assert ObservesResult(c.coordinator, v.coordinator, decision);
//              var abs := ConstantsAbstraction(c);
//              
//              /*calc {
//                  AtomicCommit.UltimateDecision(ConstantsAbstraction(c)).Commit?;
//                  forall idx:ParticipantId | ConstantsAbstraction(c).ValidParticipant(idx) :: ConstantsAbstraction(c).preferences[idx] == Yes;
//                  { 
//                    //
//                    //assert forall idx:ParticipantId | ConstantsAbstraction(c).ValidParticipant(idx) :: c.participants[idx].preference.Yes? == ConstantsAbstraction(c).preferences[idx].Yes?;
//                    }
//                
//                  forall hostIdx:ParticipantId | c.coordinator.ValidParticipantId(hostIdx) :: c.participants[hostIdx].preference.Yes?;
//                  forall hostIdx:ParticipantId | c.coordinator.ValidParticipantId(hostIdx) :: v.coordinator.votes[hostIdx].value.Yes?;
//                  decision.Commit?;
//              }
//
//              if (forall hostIdx:ParticipantId | c.coordinator.ValidParticipantId(hostIdx) :: v.coordinator.votes[hostIdx].value.Yes?) {
//                //assert forall idx | 
//                assert decision == Commit;
//                //assert forall idx | 0 <= idx < |c.coordinator.participants| ==> abs.
//                
//                assert decision == AtomicCommit.UltimateDecision(ConstantsAbstraction(c));
//
//              } else {
//                assert decision == Abort;
//                assert decision == AtomicCommit.UltimateDecision(ConstantsAbstraction(c));
//              }*/
//              
//              //assert AtomicCommit.CoordinatorLearnsDecision(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
//              assert AtomicCommit.NextStep(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), AtomicCommit.CoordinatorLearnsStep());
//              //assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
//            } else {
//              assert VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
//            }
//          }
//        }
//
//        assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
//        //} 
//      }
//      case ParticipantConstants => {
//        assert Inv(c, v');
//
//        assume AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || VariablesAbstraction(c, v) == VariablesAbstraction(c, v');
//        /*if v != v' {
//          assume AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
//        } */
//      }
//    }
//    assert Inv(c, v');
//
//    //assume AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v')) || v == v';
//    
//    /*
//    if (v != v') {
//      var step :| DistributedSystem.NextStep(c, v, v', step);
//      
//    }*/
//    //assert AtomicCommit.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'));
  }
}
