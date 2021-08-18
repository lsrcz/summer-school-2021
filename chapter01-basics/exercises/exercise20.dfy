//#title IsSeqSorted
//#desc Build an entire imperative loop method implementation with loop
//#desc invariants.

predicate IsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsSeqSorted(intSeq:seq<int>) returns (issorted:bool)
    ensures issorted <==> IsSorted(intSeq[..])
{
    var i := 0;
    issorted := true;
    while (i < |intSeq|) 
        invariant i <= |intSeq|
        invariant issorted <==> IsSorted(intSeq[0..i])
    {
        if (i != 0) {
            if (intSeq[i-1]>intSeq[i]) {
                issorted := false;
            }
        }
        i := i + 1;
    }
    return issorted;
}

