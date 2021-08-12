//#title IsPrime
//#desc Basic specification

//#start-elide
predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

//#end-elide
predicate IsPrime(i:nat)
{
//#start-elide
  && 1 < i
  && forall f :: 1 < f < i ==> !divides(f, i)
//#end-elide
}

method Main()
{
  assert !IsPrime(0);
  assert !IsPrime(1);
  assert IsPrime(2);
  assert IsPrime(3);
//#start-elide
  assert divides(2, 6);
//#end-elide
  assert !IsPrime(6);
  assert IsPrime(7);
//#start-elide
  assert divides(3, 9);
//#end-elide
  assert !IsPrime(9);
}
