// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each node has a value and at 
// most two children, which are referred to as the left child and the right child.

datatype Tree = Tree // you should define your Tree datatype here 

function method TreeAsSequence(t:Tree) : seq<int>
{
    [] // Replace me    
}

predicate IsSortedTree(t:Tree) {
    true // Replace me
}

method CheckIfSortedTree(t:Tree) returns (sorted:bool)
    ensures sorted <==> IsSortedTree(t)
{
    return true;
}

lemma ISorted(t:Tree)
    requires IsSortedTree(t) 
    ensures forall j,k | 0 <= j <= k < |TreeAsSequence(t)| :: TreeAsSequence(t)[j] <= TreeAsSequence(t)[k]
{
}

