predicate IsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsArraySorted(intary:array<int>) returns (issorted:bool)
    ensures issorted <==> IsSorted(intary[..])
{
    return true;
}

