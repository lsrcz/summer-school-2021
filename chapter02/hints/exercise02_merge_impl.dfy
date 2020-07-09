method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures IsSorted(output)
{
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    decreases |a|-ai + |b|-bi
  {
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
    }
  } 
}
