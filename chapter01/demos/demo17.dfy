// Recursion

// Let's define a function, and export properties of it with an ensures.
function CountingNumbersSeq(x:int) : (s:seq<int>)
  ensures forall i :: 0<=i<|s| ==> s[i] == i
{
  if x==0 then [] else CountingNumbersSeq(x - 1) + [x-1]
}

// Walk through this sequence

Error: cannot prove termination; try supplying a decreases clause

Try adding 'decreases x'.

Error: failure to decrease termination measure

Yeah, fix the recursive call.

Error: decreases expression must be bounded below by 0

Hmm. Add 'requires 0 <= x'.

...and then remove the decreases clause. Now Dafny can guess it!

Error: A postcondition might not hold on this return path.

Okay, now that's weird. How do we debug?
We want to use assertions, but those are statements, and we're in an
expression context.

Turns out you can insert assertions before the expression in a function.
Let's use a var (let) expression to put s in scope.
