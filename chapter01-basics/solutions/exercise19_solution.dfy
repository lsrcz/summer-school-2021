//#title FindMax
//#desc Loop invariants.

method FindMax(intSeq:seq<int>) returns (maxIndex:nat)
    requires |intSeq| > 0
    ensures maxIndex<|intSeq|
    ensures forall idx:nat | idx<|intSeq| :: intSeq[idx] <= intSeq[maxIndex]
{
    var count:nat := 0;
    maxIndex := 0;
    while(count < |intSeq|)
//#exercise        invariant true
//#exercise        invariant true
//#exercise        invariant true
//#start-elide
        invariant count <= |intSeq|
        invariant maxIndex < |intSeq|
        invariant forall prioridx:nat | prioridx<count :: intSeq[prioridx] <= intSeq[maxIndex]
//#end-elide
    {
        if(intSeq[maxIndex] < intSeq[count]) {
            maxIndex := count;
        }
        count := count+1;
    }
}
