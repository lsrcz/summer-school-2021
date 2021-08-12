//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each node has a value and at
// most two children, which are referred to as the left child and the right child.

datatype Tree = Tree // you should define your Tree datatype here

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// New syntax:  a function method is just like any other function, except it
// can be used in an "imperative" context (i.e., inside a method)

function method TreeAsSequence(t:Tree) : seq<int>
{
    [] // Replace me
}

predicate IsSortedTree(t:Tree) {
    true // Replace me
}

// You may find it useful to relate your recursive definition of IsSortedTree to
// a sequential representation of the tree structure

predicate SequenceIsSorted(s:seq<int>) {
    forall i:nat,j:nat | i<j<|s| :: s[i] <= s[j]
}

lemma SortedTreeMeansSortedSequence(t:Tree)
    requires IsSortedTree(t)
    ensures SequenceIsSorted(TreeAsSequence(t))
{
}

method CheckIfSortedTree(t:Tree) returns (sorted:bool)
    ensures sorted <==> IsSortedTree(t)
{
    return false;
}
