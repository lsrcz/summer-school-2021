//#title FindMax
//#desc Loop invariants.

method FindMax(intSeq:seq<int>) returns (maxIndex:nat)
    requires |intSeq| > 0
    ensures maxIndex<|intSeq|
    ensures forall idx:nat | idx<|intSeq| :: intSeq[idx] <= intSeq[maxIndex]
{
    var idx:nat := 0;
    maxIndex := 0;
    while(idx < |intSeq|)
//#exercise        invariant true
//#exercise        invariant true
//#exercise        invariant true
//#start-elide
        invariant idx <= |intSeq|
        invariant maxIndex < |intSeq|
        invariant forall prioridx:nat | prioridx<idx :: intSeq[prioridx] <= intSeq[maxIndex]
//#end-elide
    {
        if(intSeq[maxIndex] < intSeq[idx]) {
            maxIndex := idx;
        }
        idx := idx+1;
    }
}
