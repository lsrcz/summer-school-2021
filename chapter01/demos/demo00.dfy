// What does it mean to "prove" something? It means
// we define some concepts, and then write down a
// relation between them.
lemma EulersGraph(g:Graph)
  requires |NodesWithOddDegree(g)| > 2
  ensures !exists p :: EulerWalk(g, p)
{
  // do I want a body here? Maybe!
}

// Let's talk about code, not "just math".
// Verifier is "considering all the corner cases" -- it's not
// *trying* all 2^64; it's not a model checker! It has a model
// of the datatypes, and it reasons abstractly whether our
// claim is *always* true.
// Let's use this power to catch *all* the implementation bugs
// in your code: from low-level bugs like this one to high-level
// semantic bugs.
method Increment(a:uint64) returns (b:uint64)
  ensures b > a
{
  b := a + 1
}

method Increment(a:int) returns (b:int)
  ensures b > a
{
  b := a + 1
}



// functional programming ideas:
//  - objects are all immutable
//  - functions (vs C functions) always return the same thing:
//    mathematical substitution rule
//  - we'll stay in functional land for a few dozen exercises.
//    That's good because math is less slippery than code.
//
// assert doesn't mean "run this and crash if it doesn't hold at runtime",
// it means "confirm that this will always be true in every run of this program."
//
// pre- and post-conditions: this is the modularity mechanism.
