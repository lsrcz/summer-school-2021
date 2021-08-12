method FindMax(intary:array<int>) returns (maxIndex:nat)
    requires intary.Length > 0
    ensures maxIndex<intary.Length
    ensures forall idx:nat | idx<intary.Length :: intary[idx] <= intary[maxIndex]
{
    var idx:nat := 0;
    maxIndex := 0;
    while(idx < intary.Length)
        invariant true
        invariant true
        invariant true
    {
        if(intary[maxIndex] < intary[idx]) {
            maxIndex := idx;
        }
        idx := idx+1;
    }
}
