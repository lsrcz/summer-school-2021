// What does it mean to "prove" something? It means
// we define some concepts, and then write down a
// relation between them.
datatype Node = Node
datatype Graph = Graph
datatype Path = Path
function NodesWithOddDegree(graph:Graph) : set<Node>
predicate EulerWalk(graph:Graph, path:Path)

lemma EulersGraph(graph:Graph)
  requires |NodesWithOddDegree(graph)| > 2
  ensures !exists path :: EulerWalk(graph, path)
{
  assume false;
}

// Let's talk about code, not "just math".
// Verifier is "considering all the corner cases" -- it's not
// *trying* all 2^32; it's not a model checker! It has a model
// of the datatypes, and it reasons abstractly whether our
// claim is *always* true.
// Let's use this power to catch *all* the implementation bugs
// in your code: from low-level bugs like this one to high-level
// semantic bugs.
newtype uint32 = val:int | val < 0x1_0000_0000
method IncrementU32(val:uint32) returns (out:uint32)
  ensures out > val
{
  out := val + 1;
}

method IncrementInt(val:int) returns (output:int)
  ensures output > val
{
  output := val + 1;
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
