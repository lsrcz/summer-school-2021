predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  forall f :: 1 < f < i ==> !divides(f, i)
}

method test_prime(i:nat) returns (result:bool)
  ensures result == IsPrime(i)
{
  // Fill in the body.
}

method Main()
{
  var a := test_prime(3);
  assert a;
  var b := test_prime(4);
  assert divides(2, 4);
  assert !b;
  var c := test_prime(5);
  assert c;
}
