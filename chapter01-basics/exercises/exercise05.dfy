//#title Sets

// This predicate takes a set of integers as an argument.
// set<T> is a built-in templated type.
predicate HasSevenAndNotNine(a:set<int>)
{
  7 in a && 9 !in a
}

lemma TryOutSomeSetLiterals()
{
  assert {1,3,8} == {8,1,3};

  assert HasSevenAndNotNine({7});

  // None of these asserions are correct. Try them. Replace them with one that is.
  assert HasSevenAndNotNine({});
  assert HasSevenAndNotNine({7,9});
  assert HasSevenAndNotNine({1,3,5,7,8,9,10});
}


