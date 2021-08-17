//#title Binary Tree Search
//#desc Implement search in a binary tree and prove it works.
//#desc Practice with proof diagnosis.

include "exercise22.dfy"

// This exercise builds on exercise22 (so make sure you have completed
// that one, too). If in doubt about your solution to exercise22, contact
// an instructor during office hours to make sure you're on the right path.

method FindInBinaryTree(tree:Tree, needle:int) returns (issorted:bool)
    requires IsSortedTree(tree)
    ensures issorted <==> needle in TreeAsSequence(tree)
{
    var s := TreeAsSequence(tree);
    return needle in s;
}
