//#title FindMax
//#desc Loop invariants.

method FindMax(intary:array<int>) returns (maxIndex:nat)
    requires intary.Length > 0
    ensures maxIndex<intary.Length
    ensures forall idx:nat | idx<intary.Length :: intary[idx] <= intary[maxIndex]
{
    var idx:nat := 0;
    maxIndex := 0;
    while(idx < intary.Length)
//#exercise        invariant true
//#exercise        invariant true
//#exercise        invariant true
//#start-elide
        invariant idx <= intary.Length
        invariant maxIndex < intary.Length
        invariant forall prioridx:nat | prioridx<idx :: intary[prioridx] <= intary[maxIndex]
//#end-elide
    {
        if(intary[maxIndex] < intary[idx]) {
            maxIndex := idx;
        }
        idx := idx+1;
    }
}
