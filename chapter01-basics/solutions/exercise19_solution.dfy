method FindMax(a:array<int>) returns (maxIndex:nat)
    requires a.Length > 0
    ensures maxIndex<a.Length
    ensures forall j:nat | j<a.Length :: a[j] <= a[maxIndex]
{
    var j:nat := 0;
    maxIndex := 0;
    while(j < a.Length)
//#exercise        invariant true
//#exercise        invariant true
//#exercise        invariant true
//#start-elide
        invariant j <= a.Length
        invariant maxIndex < a.Length
        invariant forall k:nat | k<j :: a[k] <= a[maxIndex]
//#end-elide
    {
        if(a[maxIndex] < a[j]) {
            maxIndex := j;
        }
        j := j+1;
    }
}
