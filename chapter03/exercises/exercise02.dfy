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

//#elide datatype Pair = Pair(left:bool, right:bool)
datatype Variables = Variables(
//#elide     philosophers:seq<Pair>
)

predicate WellFormedConstants(c:Constants) {
    && 0 < c.tableSize 
}

predicate WellFormed(c:Constants, v:Variables) {
    && WellFormedConstants(c)
//#elide    && |v.philosophers| == c.tableSize
}

predicate Init(c:Constants, v:Variables) {
//#elide    && WellFormed(c, v)
//#elide    && (forall pi | 0 <= pi < |v.philosophers| :: v.philosophers[pi] == Pair(false, false))
}

predicate AcquireLeft(c:Constants, v:Variables, v':Variables, pi:nat) {
//#elide    && WellFormed(c, v)
//#elide    && pi < c.tableSize
//#elide    && !(v.philosophers[pi].left) // prevents this action from being a no-op
//#elide    && !(v.philosophers[PhilosopherToTheLeftOf(c,pi)].right) // comment this line to create bug
//#elide    && v' == v.(philosophers := v.philosophers[pi := Pair(true, v.philosophers[pi].right)])
}

predicate AcquireRight(c:Constants, v:Variables, v':Variables, pi:nat) {
//#elide    && WellFormed(c, v)
//#elide    && pi < c.tableSize
//#elide    && !(v.philosophers[pi].right) // prevents this action from being a no-op
//#elide    && !(v.philosophers[PhilosopherToTheRightOf(c,pi)].left) // comment this line to create bug
//#elide    && v' == v.(philosophers := v.philosophers[pi := Pair(v.philosophers[pi].left, true)])
}

predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, pi:nat) {
//#elide    && WellFormed(c, v)
//#elide    && pi < c.tableSize
//#elide    && (v.philosophers[pi].left)
//#elide    && (v.philosophers[pi].right)
//#elide    && v' == v.(philosophers := v.philosophers[pi := Pair(false, false)])
}
 
predicate Next(c:Constants, v:Variables, v':Variables) {
//#elide    exists pi:nat :: 
//#elide    (|| AcquireLeft(c, v, v', pi)
//#elide     || AcquireRight(c, v, v', pi)
//#elide     || ReleaseBoth(c, v, v', pi))
}

//#elidefunction PhilosopherToTheLeftOf(c:Constants, i:nat) : nat 
//#elide    requires WellFormedConstants(c)
//#elide{
//#elide    (i+1) % c.tableSize
//#elide}
//#elide
//#elidefunction PhilosopherToTheRightOf(c:Constants, i:nat) : nat 
//#elide    requires WellFormedConstants(c)
//#elide{
//#elide    (i-1) % c.tableSize
//#elide}
//#elide
//#elide// here is the safety property
//#elidepredicate ForkConsistency(c:Constants, v:Variables) 
//#elide{
//#elide    && WellFormed(c, v)
//#elide    && (forall i | 0 <= i < c.tableSize :: !(
//#elide        && v.philosophers[i].right 
//#elide        && v.philosophers[PhilosopherToTheRightOf(c,i)].left
//#elide        ))
//#elide}
//#elide
//#elide// here is a proof of the safety property. This lemma should verify
//#elide// without adding a body 
//#elidelemma ForkConsistencyLemma() 
//#elide    ensures forall c, v | Init(c,v) :: ForkConsistency(c, v)
//#elide    ensures forall c, v, v' | ForkConsistency(c, v) && Next(c, v, v') :: ForkConsistency(c, v')
//#elide{
//#elide}
//#elide
//#elide// this predicate and the following lemma are a way to prevent trivial
//#elide// specifications of the problem that would prevent a philosopher from
//#elide// having both forks
//#elidepredicate PhilosopherHasBothForks(c:Constants, v:Variables, pi:nat)
//#elide    requires pi < c.tableSize
//#elide    requires WellFormed(c, v)
//#elide{
//#elide    && v.philosophers[pi].left
//#elide    && v.philosophers[pi].right
//#elide}
//#elide
//#elidelemma PseudoLiveness(c:Constants, pi:nat) returns (b:seq<Variables>)
//#elide    requires c.tableSize == 3
//#elide    requires pi == 1
//#elide    ensures 0 < |b| 
//#elide    ensures Init(c, b[0])
//#elide    ensures forall i | 0 <= i < |b|-1 :: Next(c, b[i], b[i+1])
//#elide    ensures WellFormed(c, b[|b|-1])
//#elide    ensures PhilosopherHasBothForks(c, b[|b|-1], pi)
//#elide{
//#elide    var s0 := Variables([Pair(false,false), Pair(false, false), Pair(false, false)]);
//#elide    var s1 := Variables([Pair(false,false), Pair(true, false), Pair(false, false)]);
//#elide    var s2 := Variables([Pair(false,false), Pair(true, true), Pair(false, false)]);
//#elide    assert AcquireLeft(c, s0, s1, 1); // witness
//#elide    assert AcquireRight(c, s1, s2, 1); // witness
//#elide    b := [s0, s1, s2];
//#elide}
//#elide
