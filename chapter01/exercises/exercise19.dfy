method FindMax(a:array<int>) returns (maxIndex:nat)
    requires a.Length > 0
    ensures maxIndex<a.Length
    ensures forall j:nat | j<a.Length :: a[j] <= a[maxIndex]
{
    var j:nat := 0;
    maxIndex := 0;
    while(j < a.Length) 
        invariant true
        invariant true
        invariant true
    {
        if(a[maxIndex] < a[j]) {
            maxIndex := j;
        }
        j := j+1;
    }
}
