//#title Binary Search
//#desc Method implementation; writing a Hoare spec.

predicate IsSorted(seqint:seq<int>) {
    forall i:nat,j:nat | i<j<|seqint| :: seqint[i] <= seqint[j]
}

// The BinarySearch method below is a "simplified" binary search, which should return
// the index of the first element of the haystack that is >= to the needle.
// (If the needle is present, this should be the index of the needle)

method BinarySearch(haystack:array<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack[..])
//#exercise    ensures false // real spec should go here
//#exercise    ensures false // real spec should go here
//#exercise    ensures false // real spec should go here
//#start-elide
    ensures index <= haystack.Length
    ensures forall i:nat | i<index :: haystack[i] < needle
    ensures forall i:nat | index<=i<haystack.Length :: needle <= haystack[i]
//#end-elide
{
//#exercise    return 0; 
//#start-elide
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
//#end-elide
}

// The test method below helps you confirm that you wrote a meaningful specification
method Test()
{
    var ary:array<int> := new int[5];
    ary[0],ary[1],ary[2],ary[3],ary[4] := 3,6,7,7,10;
    var ret := BinarySearch(ary,7);
    assert(ret == 2);
    var ret2 := BinarySearch(ary,8);
    assert(ret2 == 4);
}

