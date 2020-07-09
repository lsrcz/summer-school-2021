// Comprehensions, the finite heuristic, axioms, recursion

predicate IsEven(x:int)
{
  x/2*2==x
}

predicate IsModest(x:int) {
  0 <= x < 10
}

// Let's do the same thing we did in the previous example, but hide the range
// constraint in a predicate IsModest.
lemma IsThisSetFinite()
{
  // Now we get:
  // Error: a set comprehension must produce a finite set, but
  // Dafny's heuristics can't figure out how to produce a bounded set of values for 'x'
//  var modestEvens := set x | IsModest(x) && IsEven(x);
//  assert modestEvens == {0,2,4,6,8};
}

// Comment out the preceding lemma so we can proceed.

// Here's one solution: rewrite modesty with a (finite) set:
function ModestNumbers() : set<int> {
  set x | 0 <= x < 10
}

lemma ThisSetIsObviouslyFinite()
{
  var modestEvens := set x | x in ModestNumbers() && IsEven(x);
  assert modestEvens == {0,2,4,6,8};
}

// But wait a second, instructor! You just moved the finite set comprehension
// inside the function!
// Yeah, so what? You got a problem with that?
// You could build the ModestNumbers set any other way you like; all dafny
// needs to use it in the modestEvents comprehension is that its value is a
// finite-set type.
// You could construct ModestEvens using recursion (which we'll do later
// when we introduce Hoare logic)
// or axiomatize it (which we'll introduce later).
