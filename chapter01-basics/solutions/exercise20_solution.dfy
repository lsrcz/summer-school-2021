predicate IsSorted(s:seq<int>) {
    forall i:nat,j:nat | i<j<|s| :: s[i] <= s[j]
}

method IsArraySorted(a:array<int>) returns (b:bool)
    ensures b <==> IsSorted(a[..])
{
    if(a.Length < 2) {
        return true;
    }
    var k:=0;
    while(k<a.Length-1) 
        invariant k <= a.Length-1
        invariant forall i:nat,j:nat | i<j<k+1 :: a[i] <= a[j]
    {
        if(a[k] > a[k+1]) {
           return false;
        }
        k := k+1;
    }
    return true;
}

