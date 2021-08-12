//#title IsPrime II
//#desc Working with an implementation proof

predicate divides(factor:nat, candidate:nat)
  requires 1<=factor
{
  candidate % factor == 0
}

predicate IsPrime(candidate:nat)
{
  && 1<candidate
  && ( forall factor :: 1 < factor < candidate ==> !divides(factor, candidate) )
}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(candidate:nat) returns (result:bool)
  requires 1<candidate
  ensures result == IsPrime(candidate)
{
  // Fill in the body.
}

method Main()
{
  var isprime3 := test_prime(3);
  assert isprime3;
  var isprime4 := test_prime(4);
  assert divides(2, 4);
  assert !isprime4;
  var isprime5 := test_prime(5);
  assert isprime5;
}
