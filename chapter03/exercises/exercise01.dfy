//#instructor This is the first state machine specification example.
//#instructor Its complexity is about the same as the library. We 
//#instructor provide the boilerplate for everything, but leave the state
//#instructor transitions as an exercise.
//#instructor It comes with a safety proof that we expect the students to use as an 
//#instructor oracle for whether they got the state transitions right.

// You are asked to define the state machine for a coke vending machine.
// The machine starts empty and has a maximum capacity of 7 cokes. 
// The machine should support the following actions:
// Purchase: dispense one coke from the machine
// Restock: add one coke to the machine

datatype Constants = Constants(capacity:int)
datatype CokeMachine = CokeMachine(numCokes:int)

predicate Init(c:Constants, cm:CokeMachine) {
//#elide    && c.capacity == 7
//#elide    && cm.numCokes == 0
}

predicate Purchase(c:Constants, cm:CokeMachine, cm':CokeMachine) {
//#elide    && cm.numCokes > 0
//#elide    && cm'.numCokes == cm.numCokes - 1
}

predicate Restock(c:Constants, cm:CokeMachine, cm':CokeMachine, numRestock:int) 
{
//#elide    && numRestock >= 0
//#elide    && cm.numCokes + numRestock <= maxCokes()
//#elide    && cm'.numCokes == cm.numCokes + numRestock
}

predicate Next(c:Constants, cm:CokeMachine, cm':CokeMachine) {
    || Purchase(c, cm, cm')
    || (exists n :: Restock(c, cm, cm', n))
} 

//==========================
// Everything below this line is not part of the specification. It allows
// you to use the verifier to confirm that your state machine has a number
// of desirable properties.

predicate Inv(c:Constants, cm:CokeMachine) {
    0 <= cm.numCokes <= c.capacity
}

lemma SafetyProof() 
    ensures forall c, cm | Init(c, cm) :: Inv(c, cm)
    ensures forall c, cm, cm' | Inv(c, cm) && Next(c, cm, cm') :: Inv(c, cm')
{
    forall cm, cm' | Inv(c, cm) && Next(c, cm, cm') 
        ensures Inv(c, cm')
    {
        if(Purchase(c, cm, cm')) {
            assert Inv(c, cm');
        } else {
            var n :| Restock(c, cm, cm', n);
            assert Inv(c, cm');
        }   
    }
}

lemma NonTrivialPurchase()
    ensures exists c, cm, cm' :: Inv(c, cm) && Next(c, cm, cm') && cm'.numCokes + 1 == cm.numCokes
{
    var c := Constants(7);
    var cm := CokeMachine(1);   
    var cm' := CokeMachine(0);   
    assert Inv(c, cm) && Next(cm, cm') && cm'.numCokes + 1 == cm.numCokes;
}

lemma NonTrivialRestock()
    ensures exists cm, cm' :: Inv(cm) && Next(cm, cm') && cm.numCokes < cm'.numCokes
{
    var c := Constants(7);
    var cm := CokeMachine(4);   
    var cm' := CokeMachine(7);   
    assert Restock(c, cm, cm', 3);
    assert Inv(c, cm) && Next(c, cm, cm') && cm.numCokes < cm'.numCokes;
}
