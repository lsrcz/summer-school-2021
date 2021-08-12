//#title Dining Philosophers
//#desc A more challenging state machine: define the state datatype.

//#elide 
//#elide 
//#elide Relative to the coke machine, the students need to
//#elide write their own datatype for philosophers and pair
//#elide (or equivalent concepts)
//#elide Introduces the constants idiom.
//#elide 
// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table. 
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step). 

datatype Constants = Constants(tableSize:nat)

//#start-elide
datatype Pair = Pair(left:bool, right:bool)
//#end-elide
//Use this datatype to define all the relevant state
//#exercisedatatype Variables = Variables()
//#start-elide
datatype Variables = Variables(philosophers:seq<Pair>)
//#end-elide

// An initial predicate to define well-formed constants.
// Feel free to add more if you need them
predicate WellFormedConstants(c:Constants) {
    && 0 < c.tableSize 
}


// An initial predicate to define well-formed state.
// Feel free to add to this predicate, if necessary
predicate WellFormed(c:Constants, v:Variables) {
    && WellFormedConstants(c)
//#start-elide
    && |v.philosophers| == c.tableSize
//#end-elide
}

predicate Init(c:Constants, v:Variables) {
//#exercise    true // Replace me
//#start-elide
    && WellFormed(c, v)
    && (forall pi | 0 <= pi < |v.philosophers| :: v.philosophers[pi] == Pair(false, false))
//#end-elide
}

// Philosopher with index pi acquires left chopstick
predicate AcquireLeft(c:Constants, v:Variables, v':Variables, pi:nat) {
//#exercise    true // Replace me
//#start-elide
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].left) // prevents this action from being a no-op
    && !(v.philosophers[PhilosopherToTheLeftOf(c,pi)].right) // comment this line to create bug
    && v' == v.(philosophers := v.philosophers[pi := Pair(true, v.philosophers[pi].right)])
//#end-elide
}

// Philosopher with index pi acquires right chopstick
predicate AcquireRight(c:Constants, v:Variables, v':Variables, pi:nat) {
//#exercise    true // Replace me
//#start-elide
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].right) // prevents this action from being a no-op
    && !(v.philosophers[PhilosopherToTheRightOf(c,pi)].left) // comment this line to create bug
    && v' == v.(philosophers := v.philosophers[pi := Pair(v.philosophers[pi].left, true)])
//#end-elide
}

// Philosopher with index pi releases both chopsticks
predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, pi:nat) {
//#exercise    true // Replace me
//#start-elide
    && WellFormed(c, v)
    && pi < c.tableSize
    && (v.philosophers[pi].left)
    && (v.philosophers[pi].right)
    && v' == v.(philosophers := v.philosophers[pi := Pair(false, false)])
//#end-elide
}
 
predicate Next(c:Constants, v:Variables, v':Variables) {
//#exercise    true // Replace me
//#start-elide
    exists pi:nat :: 
    (|| AcquireLeft(c, v, v', pi)
     || AcquireRight(c, v, v', pi)
     || ReleaseBoth(c, v, v', pi))
//#end-elide
}

//#start-elide
function PhilosopherToTheLeftOf(c:Constants, philosopher:nat) : nat 
    requires WellFormedConstants(c)
{
    (philosopher+1) % c.tableSize
}

function PhilosopherToTheRightOf(c:Constants, philosopher:nat) : nat 
    requires WellFormedConstants(c)
{
    (philosopher-1) % c.tableSize
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

lemma PseudoLiveness(c:Constants, pi:nat) returns (behavior:seq<Variables>)
    requires c.tableSize == 3
    requires pi == 1
    ensures 0 < |behavior| 
    ensures Init(c, behavior[0])
    ensures forall i | 0 <= i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1])
    ensures WellFormed(c, behavior[|behavior|-1])
    ensures PhilosopherHasBothForks(c, behavior[|behavior|-1], pi)
{
    var state0 := Variables([Pair(false,false), Pair(false, false), Pair(false, false)]);
    var state1 := Variables([Pair(false,false), Pair(true, false), Pair(false, false)]);
    var state2 := Variables([Pair(false,false), Pair(true, true), Pair(false, false)]);
    assert AcquireLeft(c, state0, state1, 1); // witness
    assert AcquireRight(c, state1, state2, 1); // witness
    behavior := [state0, state1, state2];
}
//#end-elide
