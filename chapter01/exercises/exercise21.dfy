predicate IsSorted(s:seq<int>) {
    forall i:nat,j:nat | i<j<|s| :: s[i] <= s[j]
}

// The BinarySearch method below is a "simplified" binary search, which should return
// the index of the first element of the haystack that is >= to the needle.
// (If the needle is present, this should be the index of the needle)

method BinarySearch(haystack:array<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack[..]) 
    ensures false // real spec should go here
    ensures false // real spec should go here
    ensures false // real spec should go here
{
    return 0; 
}

// The test method below helps you confirm that you wrote a meaningful specification
method Test()
{
    var a:array<int> := new int[5];
    a[0],a[1],a[2],a[3],a[4] := 3,6,7,7,10;
    var ret := BinarySearch(a,7);
    assert(ret == 2);
    var ret2 := BinarySearch(a,8);
    assert(ret2 == 4);
}

