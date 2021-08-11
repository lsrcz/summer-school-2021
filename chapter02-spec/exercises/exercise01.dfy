predicate IsPrime(i:nat)
{
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
