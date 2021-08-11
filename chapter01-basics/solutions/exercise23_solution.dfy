//#exerciseinclude "exercise22.dfy"
//#start-elide
include "exercise22_solution.dfy"
//#end-elide

// This exercise builds on exercise22 (so make sure you have completed
// that one, too). If in doubt about your solution to exercise22, contact 
// an instructor during office hours to make sure you're on the right path. 

method FindInBinaryTree(t:Tree, needle:int) returns (b:bool)
    requires IsSortedTree(t)
    ensures b <==> needle in TreeAsSequence(t)
{
//#exercise    return true;
//#start-elide
    if (t.Nil?) {
        return false;
    } else {
        if (needle == t.value) {
            return true;
        } else if (needle < t.value) {
            var leftRet := FindInBinaryTree(t.left, needle);
            return leftRet;
        } else {
            var rightRet := FindInBinaryTree(t.right, needle);
            return rightRet;
        }
    }
//#end-elide
}
