//#instructor This is the first state machine specification example.
//#instructor Its complexity is about the same as the library. We 
//#instructor provide the boilerplate for everything, but leave the state
//#instructor transitions as an exercise.
//#instructor It comes with a safety proof that we expect the students to use as an 
//#instructor oracle for whether they got the state transitions right.

datatype CokeMachine = CokeMachine(numCokes:int)

function maxCokes() : int {
   7
} 

predicate Init(cm:CokeMachine) {
    cm.numCokes == 0
}

predicate Purchase(cm:CokeMachine, cm':CokeMachine) {
//#elide    && cm.numCokes > 0
//#elide    && cm'.numCokes == cm.numCokes - 1
}

predicate Restock(cm:CokeMachine, cm':CokeMachine, numRestock:int) 
{
//#elide    && numRestock >= 0
//#elide    && cm.numCokes + numRestock <= maxCokes()
//#elide    && cm'.numCokes == cm.numCokes + numRestock
}

predicate Next(cm:CokeMachine, cm':CokeMachine) {
    || Purchase(cm, cm')
    || (exists n :: Restock(cm, cm', n))
} 

//==========================
predicate Inv(cm:CokeMachine) {
    0 <= cm.numCokes <= maxCokes()
}

lemma SafetyProof() 
    ensures forall cm | Init(cm) :: Inv(cm)
    ensures forall cm, cm' | Inv(cm) && Next(cm, cm') :: Inv(cm')
{
    forall cm, cm' | Inv(cm) && Next(cm, cm') 
        ensures Inv(cm')
    {
        if(Purchase(cm, cm')) {
            assert Inv(cm');
        } else {
            var n :| Restock(cm, cm', n);
            assert Inv(cm');
        }   
    }
}

lemma NonTrivialPurchase()
    ensures exists cm, cm' :: Inv(cm) && Next(cm, cm') && cm'.numCokes + 1 == cm.numCokes
{
    var cm := CokeMachine(1);   
    var cm' := CokeMachine(0);   
    assert Inv(cm) && Next(cm, cm') && cm'.numCokes + 1 == cm.numCokes;
}

lemma NonTrivialRestock()
    ensures exists cm, cm' :: Inv(cm) && Next(cm, cm') && cm.numCokes < cm'.numCokes
{
    var cm := CokeMachine(4);   
    var cm' := CokeMachine(7);   
    assert Restock(cm, cm', 3);
    assert Inv(cm) && Next(cm, cm') && cm.numCokes < cm'.numCokes;
}
