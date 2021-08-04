// Dining Philosophers

//#instructor 
//#instructor 
//#instructor Relative to the coke machine, the students need to
//#instructor write their own datatype for philosophers and pair
//#instructor (or equivalent concepts)
//#instructor Introduces the constants idiom.
//#instructor 

// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table. 
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step). 

datatype Constants = Constants(tableSize:nat)

datatype Pair = Pair(left:bool, right:bool)
datatype Variables = Variables(philosophers:seq<Pair>)

predicate WellFormedConstants(c:Constants) {
    && 0 < c.tableSize 
}

predicate WellFormed(c:Constants, v:Variables) {
    && WellFormedConstants(c)
    && |v.philosophers| == c.tableSize
}

predicate Init(c:Constants, v:Variables) {
    && WellFormed(c, v)
    && (forall pi | 0 <= pi < |v.philosophers| :: v.philosophers[pi] == Pair(false, false))
}

predicate AcquireLeft(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].left) // prevents this action from being a no-op
    && !(v.philosophers[PhilosopherToTheLeftOf(c,pi)].right) // comment this line to create bug
    && v' == v.(philosophers := v.philosophers[pi := Pair(true, v.philosophers[pi].right)])
}

predicate AcquireRight(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].right) // prevents this action from being a no-op
    && !(v.philosophers[PhilosopherToTheRightOf(c,pi)].left) // comment this line to create bug
    && v' == v.(philosophers := v.philosophers[pi := Pair(v.philosophers[pi].left, true)])
}

predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && (v.philosophers[pi].left)
    && (v.philosophers[pi].right)
    && v' == v.(philosophers := v.philosophers[pi := Pair(false, false)])
}
 
predicate Next(c:Constants, v:Variables, v':Variables) {
    exists pi:nat :: 
    (|| AcquireLeft(c, v, v', pi)
     || AcquireRight(c, v, v', pi)
     || ReleaseBoth(c, v, v', pi))
}

function PhilosopherToTheLeftOf(c:Constants, i:nat) : nat 
    requires WellFormedConstants(c)
{
    (i+1) % c.tableSize
}

function PhilosopherToTheRightOf(c:Constants, i:nat) : nat 
    requires WellFormedConstants(c)
{
    (i-1) % c.tableSize
}

// here is the safety property
predicate ForkConsistency(c:Constants, v:Variables) 
{
    && WellFormed(c, v)
    && (forall i | 0 <= i < c.tableSize :: !(
        && v.philosophers[i].right 
        && v.philosophers[PhilosopherToTheRightOf(c,i)].left
        ))
}

// here is a proof of the safety property. This lemma should verify
// without adding a body 
lemma ForkConsistencyLemma() 
    ensures forall c, v | Init(c,v) :: ForkConsistency(c, v)
    ensures forall c, v, v' | ForkConsistency(c, v) && Next(c, v, v') :: ForkConsistency(c, v')
{
}

// this predicate and the following lemma are a way to prevent trivial
// specifications of the problem that would prevent a philosopher from
// having both forks
predicate PhilosopherHasBothForks(c:Constants, v:Variables, pi:nat)
    requires pi < c.tableSize
    requires WellFormed(c, v)
{
    && v.philosophers[pi].left
    && v.philosophers[pi].right
}

lemma PseudoLiveness(c:Constants, pi:nat) returns (b:seq<Variables>)
    requires c.tableSize == 3
    requires pi == 1
    ensures 0 < |b| 
    ensures Init(c, b[0])
    ensures forall i | 0 <= i < |b|-1 :: Next(c, b[i], b[i+1])
    ensures WellFormed(c, b[|b|-1])
    ensures PhilosopherHasBothForks(c, b[|b|-1], pi)
{
    var s0 := Variables([Pair(false,false), Pair(false, false), Pair(false, false)]);
    var s1 := Variables([Pair(false,false), Pair(true, false), Pair(false, false)]);
    var s2 := Variables([Pair(false,false), Pair(true, true), Pair(false, false)]);
    assert AcquireLeft(c, s0, s1, 1); // witness
    assert AcquireRight(c, s1, s2, 1); // witness
    b := [s0, s1, s2];
}

