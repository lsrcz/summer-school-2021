// Here's the body of test_prime. It's correct (you're welcome),
// but the proof won't go through yet.
method test_prime(i:nat) returns (result:bool)
    ensures result == IsPrime(i)
{
  // Three of these lines are the while version of for(f=0; f<i; f++){}.
  var f := 2;
  while (f < i)
  {
    // If this factor divides i, we've found a counterexample;
    // i isn't prime.
    if i % f == 0 {
      return false;
    }
    f := f + 1;
  }
  // We tested every possible factor, and none divided i. i is prime.
  return true;
}
