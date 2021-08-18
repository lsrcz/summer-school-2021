//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each (internal) node has a value and at
// most two children, which are referred to as the left child and the right child.

datatype Tree = Leaf(v:int) | Node(v:int, l:Tree, r:Tree)

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// New syntax:  a function method is just like any other function, except it
// can be used in an "imperative" context (i.e., inside a method)

function method TreeAsSequence(tree:Tree) : seq<int>
{
    match tree
      case Leaf(v) => [v]
      case Node(v, l, r) => TreeAsSequence(l) + [v] + TreeAsSequence(r)
}

// Note: Don't use SequenceIsSorted in your definition of IsSortedTree.
predicate IsSortedTree(tree:Tree) {
    SequenceIsSorted(TreeAsSequence(tree))
}

// You may find it useful to relate your recursive definition of IsSortedTree to
// a sequential representation of the tree structure

predicate SequenceIsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

lemma SortedTreeMeansSortedSequence(tree:Tree)
    requires IsSortedTree(tree)
    ensures SequenceIsSorted(TreeAsSequence(tree))
{
}

// Write a recursive implementation that checks if a tree
// is sorted by checking the children, then using TreeAsSequence
// on the children to confirm that both children stay on their
// respective sides of the pivot.
method CheckIfSortedTree(tree:Tree) returns (sorted:bool)
    ensures sorted <==> IsSortedTree(tree)
{
    var s := TreeAsSequence(tree);
    var i := 0;
    sorted := true;
    while (i < |s|) 
        invariant i <= |s|
        invariant sorted <==> SequenceIsSorted(s[0..i])
    {
        if (i != 0) {
            if (s[i-1]>s[i]) {
                sorted := false;
            }
        }
        i := i + 1;
    }
    return sorted;
}
