// Recursion challenge.

function method fibo(i:nat) : nat
{
//#exercise  0
//#start-elide
  if i == 0 then 0
  else if i == 1 then 1
  else fibo(i-2) + fibo(i-1)
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
