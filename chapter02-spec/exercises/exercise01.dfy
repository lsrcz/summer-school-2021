//#title IsPrime I
//#desc Basic specification.
// Implement a predicate that tells whether a natural number is prime.

predicate IsPrime(candidate:nat)
{
  && false // Replace me
}

method Main()
{
  assert !IsPrime(0);
  assert !IsPrime(1);
  assert IsPrime(2);
  assert IsPrime(3);
  assert !IsPrime(6);
  assert IsPrime(7);
  assert !IsPrime(9);
}
