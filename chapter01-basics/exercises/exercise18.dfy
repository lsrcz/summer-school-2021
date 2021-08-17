//#title Fibo
//#desc Recursion challenge.

function method fibo(val:nat) : nat
{
  if (val == 0) then 
    0
  else if (val == 1) then
    1
  else
    fibo(val - 1) + fibo(val - 2)
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(20) == 6765
{
}
