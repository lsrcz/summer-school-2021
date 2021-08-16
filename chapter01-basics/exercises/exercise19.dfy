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
        invariant true
        invariant true
        invariant true
    {
        if(intSeq[maxIndex] < intSeq[idx]) {
            maxIndex := idx;
        }
        idx := idx+1;
    }
}
