predicate IsSorted(s:seq<int>) {
    forall i:nat,j:nat | i<j<|s| :: s[i] <= s[j]
}

method BinarySearch(haystack:array<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack[..])
    ensures index <= haystack.Length
    ensures forall i:nat | i<index :: haystack[i] < needle
    ensures forall i:nat | index<=i<haystack.Length :: needle <= haystack[i]
{
    var low:nat := 0;
    var high:nat := haystack.Length;
     
    while(low < high)
        invariant low <= high <= haystack.Length 
        invariant forall i:nat | i < low :: haystack[i] < needle
        invariant forall i:nat | high <= i < haystack.Length :: needle <= haystack[i]
    {
        var mid := (low+high)/2;
        if(haystack[mid] < needle) {
            low := mid+1;
        } else {
            high := mid;
        }
        
    }
    return low; 
}

