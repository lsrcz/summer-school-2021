predicate IsSorted(s:seq<int>) {
    forall i:nat,j:nat | i<j<|s| :: s[i] <= s[j]
}

method IsArraySorted(a:array<int>) returns (b:bool)
    ensures b <==> IsSorted(a[..])
{
    return true;
}

