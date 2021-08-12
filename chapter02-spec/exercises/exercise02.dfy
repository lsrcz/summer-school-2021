//#title IsPrime
//#desc Working with an implementation proof

predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(i:nat) returns (result:bool)
  requires 1<i
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
