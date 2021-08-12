//#title IsArraySorted
//#desc Build an entire imperative loop method implementation with loop
//#desc invariants.

predicate IsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsArraySorted(intary:array<int>) returns (issorted:bool)
    ensures issorted <==> IsSorted(intary[..])
{
//#exercise    return true;
//#start-elide
    if(intary.Length < 2) {
        return true;
    }
    var idx:=0;
    while(idx<intary.Length-1) 
        invariant idx <= intary.Length-1
        invariant forall i:nat,j:nat | i<j<idx+1 :: intary[i] <= intary[j]
    {
        if(intary[idx] > intary[idx+1]) {
           return false;
        }
        idx := idx+1;
    }
    return true;
//#end-elide
}

