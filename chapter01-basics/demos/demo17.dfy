// Recursion

// Let's define a function, and export properties of it with an ensures.
/*
function Evens(count:int) : (outseq:seq<int>)
  ensures forall idx :: 0<=idx<|outseq| ==> outseq[idx] == 2 * idx
{
  if count==0 then [] else Evens(count) + [2 * (count-1)]
}
*/

function EvensOk(count:int) : (outseq:seq<int>)
  requires 0 <= count
  ensures count == |outseq|
  ensures forall idx :: 0<=idx<|outseq| ==> outseq[idx] == 2 * idx
{
  var outseq := if count==0 then [] else EvensOk(count - 1) + [2 * (count-1)];
  outseq
}

// Walk through this sequence
/*
Error: cannot prove termination; try supplying a decreases clause

Try adding 'decreases count'.

Error: failure to decrease termination measure

Yeah, fix the recursive call.

Error: decreases expression must be bounded below by 0

Hmm. Add 'requires 0 <= count'.

...and then remove the decreases clause. Now Dafny can guess it!

Error: A postcondition might not hold on this return path.

Okay, now that's weird. How do we debug?
We want to use assertions, but those are statements, and we're in an
expression context.

Turns out you can insert assertions before the expression in a function.
Let's use a var (let) expression to put outseq in scope.

Punchline: it doesn't know |outseq|==count

*/