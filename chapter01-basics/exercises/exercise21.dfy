//#title Binary Search
//#desc Method implementation; writing a Hoare spec.

predicate IsSorted(seqint:seq<int>) {
    forall i:nat,j:nat | i<j<|seqint| :: seqint[i] <= seqint[j]
}

// The BinarySearch method below is a "simplified" binary search, which should return
// the index of the first element of the haystack that is >= to the needle.
// (If the needle is present, this should be the index of the needle)

method BinarySearch(haystack:seq<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack)
    ensures 0<=index<=|haystack|
    ensures forall i:int | 0<=i<index :: haystack[i] < needle// real spec should go here
    ensures forall i:int | index<=i<|haystack| :: haystack[i]>=needle // real spec should go here
{
    if (|haystack|==0) {
        return 0;
    } else {
        var mid := |haystack| / 2;
        var sl := haystack[..mid];
        var sr := haystack[mid+1..];

        if (haystack[mid] >= needle) {
            index := BinarySearch(sl, needle);
            return index;
        } else {
            var r1 := BinarySearch(sr, needle);
            index := r1 + mid + 1;
            return index;
        }
    }
}

// The test method below helps you confirm that you wrote a meaningful specification
method Test()
{
    var sq:seq<int> := [3,6,7,7,10];
    var ret := BinarySearch(sq,7);
    assert sq[1] < 7 <= sq[2];  // trigger
    assert ret == 2;
    var ret2 := BinarySearch(sq,8);
    assert sq[3] < 8 <= sq[4];  // trigger
    assert ret2 == 4;
}

