//#title Set comprehensions, maps

predicate IsEven(x:int)
{
  x/2*2==x
}

lemma SetComprehension()
{
  var modestEvens := set x | 0 <= x < 10 && IsEven(x);
  assert modestEvens == {0,2,4,6,8};
}

lemma Maps()
{
  // Map generic type, map literal syntax
  var doubleMap:map<int, int> := map[1:=2, 2:=4, 3:=6, 4:=8];

  assert doubleMap[3] == 6;

  var replaceMap := doubleMap[3 := 7];
  assert replaceMap[1] == 2;
  assert replaceMap[2] == 4;
//#exercise  assert replaceMap[3] == 6;
//#start-elide
  assert replaceMap[3] == 7;
//#end-elide
}
