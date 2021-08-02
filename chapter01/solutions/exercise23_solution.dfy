include "exercise22_solution.dfy"

method FindInBinaryTree(t:Tree, needle:int) returns (b:bool)
    requires IsSortedTree(t)
    ensures b <==> needle in TreeAsSequence(t)
{
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
}
