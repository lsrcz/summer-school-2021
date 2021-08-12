//#title Coke Machine
//#desc The first state machine specification exercise: fill in actions.

// You are asked to define the state machine for a coke vending machine.
// The machine starts empty and has a maximum capacity of 7 cokes.
// The machine should support the following actions:
// Purchase: dispense one coke from the machine
// Restock: add one coke to the machine

datatype Constants = Constants(capacity:int)
datatype CokeMachine = CokeMachine(numCokes:int)

predicate Init(c:Constants, v:CokeMachine) {
    true // Replace me
}

predicate Purchase(c:Constants, v:CokeMachine, v':CokeMachine) {
    true // Replace me
}

predicate Restock(c:Constants, v:CokeMachine, v':CokeMachine, numRestock:int)
{
    true // Replace me
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
    assert Inv(c, v) && Next(c, v, v') && v'.numCokes + 1 == v.numCokes;
}

lemma NonTrivialRestock()
    ensures exists c, v, v' :: Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes
{
    var c := Constants(7);
    var v := CokeMachine(4);
    var v' := CokeMachine(7);
    assert Restock(c, v, v', 3);
    assert Inv(c, v) && Next(c, v, v') && v.numCokes < v'.numCokes;
}
