//#title IsPrime I
//#desc Basic specification.
// Implement a predicate that tells whether a natural number is prime.

predicate CanDivide(factor: nat, candidate: nat)
  requires factor != 0
{
    candidate % factor == 0
}

predicate IsPrime(candidate:nat)
{
  candidate >= 2 && forall x:nat | 2 <= x < candidate :: !CanDivide(x, candidate)
}

method Main()
{
  assert !IsPrime(0);
  assert !IsPrime(1);
  assert IsPrime(2);
  assert IsPrime(3);

  assert CanDivide(2, 6);
  assert !IsPrime(6);
  assert IsPrime(7);
  assert CanDivide(3, 9);
  assert !IsPrime(9);
}
