datatype Tree = Nil | Node(value:int, left:Tree, right:Tree)

function method I(t:Tree) : seq<int>
{
    if t.Nil? then []
    else I(t.left) + [t.value] + I(t.right)
}

predicate IsSortedTree(t:Tree) {
    if (t.Nil?) 
    then true 
    else
        && (forall j | 0 <= j < |I(t.left)| :: I(t.left)[j] <= t.value)
        && (forall j | 0 <= j < |I(t.right)| :: t.value <= I(t.right)[j])
        && IsSortedTree(t.left)
        && IsSortedTree(t.right)
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
            var leftSeq := I(t.left);
            var rightSeq := I(t.right);
            var isValueAfterLeft:bool := |leftSeq| == 0 || leftSeq[|leftSeq|-1] <= t.value;
            var isValueBeforeRight:bool := |rightSeq| == 0 || t.value <= rightSeq[0];
            if(!isValueAfterLeft) {
                return false;
            } else if (!isValueBeforeRight) {
                return false;
            } else {
                ISorted(t.left);
                ISorted(t.right);
                return true;
            }
        }    
    }
}

lemma ISorted(t:Tree)
    requires IsSortedTree(t) 
    ensures forall j,k | 0 <= j <= k < |I(t)| :: I(t)[j] <= I(t)[k]
{
}

