//#title Merge Sort
//#desc More specification practice.

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures IsSorted(output)
{
  // Supply the body.
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
  ensures IsSorted(output)
{
  // Supply the body.
}
