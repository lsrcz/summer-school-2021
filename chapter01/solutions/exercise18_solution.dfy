function method fibo(i:nat) : nat
{
  if i == 0 then 0
  else if i == 1 then 1
  else fibo(i-2) + fibo(i-1)
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
    var f := fibo(x);
    print x, " ", f, "\n";
    x := x + 1;
  }
}
