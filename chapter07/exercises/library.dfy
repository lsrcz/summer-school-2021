module Library {
  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {
    theSeq[..|theSeq|-1]
  }

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {
    theSeq[|theSeq|-1]
  }

  function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  {
    if |theSets| == 0 then {} else
      UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  // As you can see, Dafny's recursion heuristics easily complete the recursion
  // induction proofs, so these two statements could easily be ensures of
  // UnionSeqOfSets. However, the quantifiers combine with native map axioms
  // to be a bit trigger-happy, so we've pulled them into independent lemmas
  // you can invoke only when needed.
  lemma SetsAreSubsetsOfUnion<T>(theSets: seq<set<T>>)
    ensures forall idx | 0<=idx<|theSets| :: theSets[idx] <= UnionSeqOfSets(theSets)
  {
  }

  lemma EachUnionMemberBelongsToASet<T>(theSets: seq<set<T>>)
    ensures forall member | member in UnionSeqOfSets(theSets) ::
          exists idx :: 0<=idx<|theSets| && member in theSets[idx]
  {
  }

  // Convenience function for learning a particular index (invoking Hilbert's
  // Choose on the exists in EachUnionMemberBelongsToASet).
  lemma GetIndexForMember<T>(theSets: seq<set<T>>, member: T) returns (idx:int)
    requires member in UnionSeqOfSets(theSets)
    ensures 0<=idx<|theSets|
    ensures member in theSets[idx]
  {
    EachUnionMemberBelongsToASet(theSets);
    var chosenIdx :| 0<=chosenIdx<|theSets| && member in theSets[chosenIdx];
    idx := chosenIdx;
  }
}
