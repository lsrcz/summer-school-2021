//#title IsSorted
//#desc More specification practice.

predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures IsSorted(output)
{
  // Supply the body.
}

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures IsSorted(output)
{
  // Supply the body.
}
