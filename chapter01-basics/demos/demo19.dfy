function method fibo(val:nat) : nat
{
  if val == 0 then 0
  else if val == 1 then 1
  else fibo(val-2) + fibo(val-1)
}

method fastfibo(val:nat) returns (fibout:nat)
  ensures fibo(val) == fibout
{
  if val==0 {
    fibout := 0;
    return;
  }

  var prevfib := 0;
  var curfib := 1;
  var idx := 1;

  while idx < val
    invariant idx <= val
    invariant prevfib == fibo(idx-1)
    invariant curfib == fibo(idx)
  {
    var nextfib := prevfib + curfib;
    prevfib := curfib;
    curfib := nextfib;
    idx := idx + 1;
  }

  fibout := curfib;
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(49) == 7778742049
{
}

method Main()
{
  var val := 0;
  while val < 50 {
    var f := fastfibo(val);
    print val, " ", f, "\n";
    val := val + 1;
  }
}
