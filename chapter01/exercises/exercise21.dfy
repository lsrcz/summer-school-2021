predicate IsSorted(s:seq<int>) {
    forall i:nat,j:nat | i<j<|s| :: s[i] <= s[j]
}

method BinarySearch(haystack:array<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack[..]) 
    ensures false // real spec should go here
    ensures false // real spec should go here
    ensures false // real spec should go here
{
    return 0; 
}

