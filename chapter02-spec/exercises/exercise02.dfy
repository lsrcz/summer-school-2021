//#title IsPrime II
//#desc Working with an implementation proof

// Here's a correct definition of IsPrime.
// Take another little detour to implementation-land by writing a method
// `test_prime` that implements IsPrime with an imperative while() loop.

predicate method divides(factor:nat, candidate:nat)
  requires 1<=factor
{
  candidate % factor == 0
}

predicate IsPrime(candidate:nat)
{
  && 1<candidate
  && ( forall factor :: 1 < factor < candidate ==> !divides(factor, candidate) )
}

/*
What does it mean by
"return statement is not allowed in this context (because it is guarded by a specification-only expression)"
*/
// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(candidate:nat) returns (result:bool)
  requires 1<candidate
  ensures result == IsPrime(candidate)
{
    var factor := 2;

    while (factor < candidate)
      invariant forall factor1:nat | 1 < factor1 < factor :: !divides(factor1, candidate)
    {
      var divides_result := divides(factor, candidate);
      if (divides_result) {
        return false;
      }
      factor := factor + 1;
    }
    assert IsPrime(candidate);
    return true;
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
