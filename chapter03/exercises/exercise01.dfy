// Coke Machine
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

predicate Init(c:Constants, v:CokeMachine) {
//#elide    && c.capacity == 7
//#elide    && v.numCokes == 0
    true // replace me
}

predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) {
//#elide    && v.numCokes > 0
//#elide    && v'.numCokes == v.numCokes - 1
    true // replace me
}

predicate Restock(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int) 
{
//#elide    && numRestock >= 0
//#elide    && v.numCokes + numRestock <= maxCokes()
//#elide    && v'.numCokes == v.numCokes + numRestock
    true // replace me
}

predicate Next(c:Constants, v:CokeMachine, v':CokeMachine) {
    || Purchase(c, v, v')
    || (exists n :: Restock(c, v, v', n))
} 

//==========================
// Everything below this line is not part of the specification. It allows
// you to use the verifier to confirm that your state machine has a number
// of desirable properties.

predicate Inv(c:Constants, v:CokeMachine) {
    0 <= v.numCokes <= c.capacity
}

lemma SafetyProof() 
    ensures forall c, v | Init(c, v) :: Inv(c, v)
    ensures forall c, v, v' | Inv(c, v) && Next(c, v, v') :: Inv(c, v')
{
    forall c, v, v' | Inv(c, v) && Next(c, v, v') 
        ensures Inv(c, v')
    {
        if(Purchase(c, v, v')) {
            assert Inv(c, v');
        } else {
            var n :| Restock(c, v, v', n);
            assert Inv(c, v');
        }   
    }
}

lemma NonTrivialPurchase()
    ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes
{
    var c := Constants(7);
    var v := CokeMachine(1);   
    var v' := CokeMachine(0);   
    assert Inv(c, v) && Next(v, v') && v'.numCokes + 1 == v.numCokes;
}

lemma NonTrivialRestock()
    ensures exists v, v' :: Inv(v) && Next(v, v') && v.numCokes < v'.numCokes
{
    var c := Constants(7);
    var v := CokeMachine(4);   
    var v' := CokeMachine(7);   
    assert Restock(c, v, v', 3);
    assert Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes;
}
