//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each node has a value and at
// most two children, which are referred to as the left child and the right child.

//#exercisedatatype Tree = Tree // you should define your Tree datatype here
//#start-elide
datatype Tree = Nil | Node(value:int, left:Tree, right:Tree)
//#end-elide

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// New syntax:  a function method is just like any other function, except it
// can be used in an "imperative" context (i.e., inside a method)

function method TreeAsSequence(t:Tree) : seq<int>
{
//#exercise    [] // Replace me
//#start-elide
    if t.Nil? then []
    else TreeAsSequence(t.left) + [t.value] + TreeAsSequence(t.right)
//#end-elide
}

predicate IsSortedTree(t:Tree) {
//#exercise    true // Replace me
//#start-elide
    if (t.Nil?)
    then true
    else
        && (forall j | 0 <= j < |TreeAsSequence(t.left)| :: TreeAsSequence(t.left)[j] <= t.value)
        && (forall j | 0 <= j < |TreeAsSequence(t.right)| :: t.value <= TreeAsSequence(t.right)[j])
        && IsSortedTree(t.left)
        && IsSortedTree(t.right)
//#end-elide
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
//#exercise    return false;
//#start-elide
    if (t.Nil?) {
        return true;
    } else {
        var leftSorted := CheckIfSortedTree(t.left);
        var rightSorted := CheckIfSortedTree(t.right);
        if (!leftSorted || !rightSorted) {
            assert !IsSortedTree(t);
            return false;
        } else {
            var leftSeq := TreeAsSequence(t.left);
            var rightSeq := TreeAsSequence(t.right);
            var isValueAfterLeft:bool := |leftSeq| == 0 || leftSeq[|leftSeq|-1] <= t.value;
            var isValueBeforeRight:bool := |rightSeq| == 0 || t.value <= rightSeq[0];
            if(!isValueAfterLeft) {
                return false;
            } else if (!isValueBeforeRight) {
                return false;
            } else {
                SortedTreeMeansSortedSequence(t.left);
                SortedTreeMeansSortedSequence(t.right);
                return true;
            }
        }
    }
//#end-elide
}
