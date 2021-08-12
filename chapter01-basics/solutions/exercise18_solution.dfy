//#title Fibo
//#desc Recursion challenge.

function method fibo(val:nat) : nat
{
//#exercise  0
//#start-elide
  if val == 0 then 0
  else if val == 1 then 1
  else fibo(val-2) + fibo(val-1)
//#end-elide
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(20) == 6765
{
}
//#start-elide
// Here's the setup for the fast-fibo demo.

method Main()
{
  var x := 0;
  while x < 50 {
    var f := fibo(x);
    print x, " ", f, "\n";
    x := x + 1;
  }
}
//#end-elide
