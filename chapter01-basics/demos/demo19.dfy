function method fibo(i:nat) : nat
{
  if i == 0 then 0
  else if i == 1 then 1
  else fibo(i-2) + fibo(i-1)
}

method fastfibo(i:nat) returns (f:nat)
  ensures fibo(i) == f
{
  if i==0 {
    f := 0;
    return;
  }

  var a := 0;
  var b := 1;
  var j := 1;

  while j < i
    invariant j <= i
    invariant a == fibo(j-1)
    invariant b == fibo(j)
  {
    var c := a + b;
    a := b;
    b := c;
    j := j + 1;
  }

  f := b;
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(49) == 7778742049
{
}

method Main()
{
  var x := 0;
  while x < 50 {
    var f := fastfibo(x);
    print x, " ", f, "\n";
    x := x + 1;
  }
}
