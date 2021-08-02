datatype Tree = Nil | Node(value:int, left:Tree, right:Tree)

function method TreeAsSequence(t:Tree) : seq<int>
{
    if t.Nil? then []
    else TreeAsSequence(t.left) + [t.value] + TreeAsSequence(t.right)
}

predicate IsSortedTree(t:Tree) {
    if (t.Nil?) 
    then true 
    else
        && (forall j | 0 <= j < |TreeAsSequence(t.left)| :: TreeAsSequence(t.left)[j] <= t.value)
        && (forall j | 0 <= j < |TreeAsSequence(t.right)| :: t.value <= TreeAsSequence(t.right)[j])
        && IsSortedTree(t.left)
        && IsSortedTree(t.right)
}

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
}


