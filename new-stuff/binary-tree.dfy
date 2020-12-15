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
            // TBD
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
                forall j | 0 <= j < |I(t.left)| 
                    ensures I(t.left)[j] <= t.value
                {
                    if (|leftSeq| == 0) {
                        assert I(t.left)[j] <= t.value;
                    } else {
                        assert IsSortedTree(t.left);
                        assert !t.left.Nil?;
                        ISorted(t.left);
                        assert (forall j | 0 <= j < |I(t.left)| :: I(t.left)[j] <= t.value);
                        assert I(t.left)[j] <= t.value;
                    }
                }
                ISorted(t.right);
                assert (forall j | 0 <= j < |I(t.right)| :: t.value <= I(t.right)[j]);
                return true;
            }
        }    
    }
}

lemma ISorted(t:Tree)
    requires IsSortedTree(t) 
    ensures forall j,k | 0 <= j <= k < |I(t)| :: I(t)[j] <= I(t)[k]
{
    // TBD
}

