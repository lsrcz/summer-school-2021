include "exercise22.dfy"

// This exercise builds on exercise22 (so make sure you have completed
// that one, too). If in doubt about your solution to exercise22, contact 
// an instructor during office hours to make sure you're on the right path. 

method FindInBinaryTree(t:Tree, needle:int) returns (b:bool)
    requires IsSortedTree(t)
    ensures b <==> needle in TreeAsSequence(t)
{
    return true;
}
