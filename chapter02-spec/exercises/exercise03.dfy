//#title Merge Sort
//#desc More specification practice.

// Implement a merge sort that guarantees the result is sorted.
// merge() sohuld merge its two sorted inputs into a sorted output.
// merge_sort picks a pivot, recursively merge_sort()s the subsequences,
// and then uses merge() to put them back together. We've provided
// signatures for merge and merge_sort to get you started.

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures IsSorted(output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    if left!=[] {
      left := merge_sort(left);
    }
    if right!=[] {
      right := merge_sort(right);
    }
    output := merge(left, right);
  }
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
  ensures IsSorted(output)
{
  var idxa := 0;
  var idxb := 0;
  output := [];
  while idxa < |seqa| || idxb < |seqb|
    invariant idxa <= |seqa|
    invariant idxb <= |seqb|
    invariant |output| > 0 && idxa < |seqa| ==> output[|output| - 1] <= seqa[idxa]
    invariant |output| > 0 && idxb < |seqb| ==> output[|output| - 1] <= seqb[idxb]
    invariant IsSorted(output)
    decreases |seqa| - idxa + |seqb| - idxb
  {
    if idxa == |seqa| || (idxb < |seqb| && seqa[idxa] >= seqb[idxb]) {
      output := output + [seqb[idxb]];
      idxb := idxb + 1;
    } else {
      output := output + [seqa[idxa]];
      idxa := idxa + 1;
    }
  }
}
