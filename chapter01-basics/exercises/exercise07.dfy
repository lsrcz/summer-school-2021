//#title Sequences

lemma ExperimentsWithSequences()
{
  // [t] is a literal sequence; this one is a seq<int>.
  var fibo := [1,1,2,3,5,8,13,21,34];
  // Index into a set.
  assert fibo[4] == 5;

  // Sequences have cardinality (and hence are always finite length).
  assert |fibo| == 9;
  assert fibo[0] == 1;
  assert fibo[8] == 34;
  assert fibo[9] == 55;

  // A slice of a sequence is a sequence.
  // The left argument is inclusive, the right exclusive.
  assert fibo[2..4] == [2,3];

  // You can omit either endpoint to refer to the beginning or end of the
  // sequence.
  assert fibo[..3] == [1,1,2];
  assert fibo[7..] == [21,34];

  assert |fibo[2..5]| == 4;

  assert false; // Comment out this line, and uncomment the next to proceed. Read the error message. Fix it.
//  assert fibo[5..6] == 8;

  // The type of fibo is seq<int>.
  // Here, we explicitly declare the type of `copy`. In previous examples, the
  // type has always been inferred by the compiler. I just wanted you to see
  // what it was inferring.
  var copy:seq<int> := fibo;

  // You can, of course, have a seq of other stuff.
  var seqOfSets:seq<set<int>> := [{0}, {0,1}, {0,1,2}];

// TRY IT: Uncomment this line. Read the error message. Fix it.
//  var whatsMyProblem := [0, false];

  // |expr| below is sequence-length
  assert |seqOfSets| == 3;
  // Type checking means the |expr| below is a set-cardinality operator.
  assert |seqOfSets[1]| == 3;
}

