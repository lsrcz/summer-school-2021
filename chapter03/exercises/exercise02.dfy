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
datatype State = State(
//#elide     philosophers:seq<Pair>
)

predicate WellFormedConstants(c:Constants) {
    && 0 < c.tableSize 
}

predicate WellFormed(c:Constants, s:State) {
    && WellFormedConstants(c)
//#elide    && |s.philosophers| == c.tableSize
}

predicate Init(c:Constants, s:State) {
//#elide    && WellFormed(c, s)
//#elide    && (forall pi | 0 <= pi < |s.philosophers| :: s.philosophers[pi] == Pair(false, false))
}

predicate AcquireLeft(c:Constants, s:State, s':State, pi:nat) {
//#elide    && WellFormed(c, s)
//#elide    && pi < c.tableSize
//#elide    && !(s.philosophers[pi].left) // prevents this action from being a no-op
//#elide    && !(s.philosophers[PhilosopherToTheLeftOf(c,pi)].right) // comment this line to create bug
//#elide    && s' == s.(philosophers := s.philosophers[pi := Pair(true, s.philosophers[pi].right)])
}

predicate AcquireRight(c:Constants, s:State, s':State, pi:nat) {
//#elide    && WellFormed(c, s)
//#elide    && pi < c.tableSize
//#elide    && !(s.philosophers[pi].right) // prevents this action from being a no-op
//#elide    && !(s.philosophers[PhilosopherToTheRightOf(c,pi)].left) // comment this line to create bug
//#elide    && s' == s.(philosophers := s.philosophers[pi := Pair(s.philosophers[pi].left, true)])
}

predicate ReleaseBoth(c:Constants, s:State, s':State, pi:nat) {
//#elide    && WellFormed(c, s)
//#elide    && pi < c.tableSize
//#elide    && (s.philosophers[pi].left)
//#elide    && (s.philosophers[pi].right)
//#elide    && s' == s.(philosophers := s.philosophers[pi := Pair(false, false)])
}
 
predicate Next(c:Constants, s:State, s':State) {
//#elide    exists pi:nat :: 
//#elide    (|| AcquireLeft(c, s, s', pi)
//#elide     || AcquireRight(c, s, s', pi)
//#elide     || ReleaseBoth(c, s, s', pi))
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
//#elidepredicate ForkConsistency(c:Constants, s:State) 
//#elide{
//#elide    && WellFormed(c, s)
//#elide    && (forall i | 0 <= i < c.tableSize :: !(
//#elide        && s.philosophers[i].right 
//#elide        && s.philosophers[PhilosopherToTheRightOf(c,i)].left
//#elide        ))
//#elide}
//#elide
//#elide// here is a proof of the safety property. This lemma should verify
//#elide// without adding a body 
//#elidelemma ForkConsistencyLemma() 
//#elide    ensures forall c, s | Init(c,s) :: ForkConsistency(c, s)
//#elide    ensures forall c, s, s' | ForkConsistency(c, s) && Next(c, s, s') :: ForkConsistency(c, s')
//#elide{
//#elide}
//#elide
//#elide// this predicate and the following lemma are a way to prevent trivial
//#elide// specifications of the problem that would prevent a philosopher from
//#elide// having both forks
//#elidepredicate PhilosopherHasBothForks(c:Constants, s:State, pi:nat)
//#elide    requires pi < c.tableSize
//#elide    requires WellFormed(c, s)
//#elide{
//#elide    && s.philosophers[pi].left
//#elide    && s.philosophers[pi].right
//#elide}
//#elide
//#elidelemma PseudoLiveness(c:Constants, pi:nat) returns (b:seq<State>)
//#elide    requires c.tableSize == 3
//#elide    requires pi == 1
//#elide    ensures 0 < |b| 
//#elide    ensures Init(c, b[0])
//#elide    ensures forall i | 0 <= i < |b|-1 :: Next(c, b[i], b[i+1])
//#elide    ensures WellFormed(c, b[|b|-1])
//#elide    ensures PhilosopherHasBothForks(c, b[|b|-1], pi)
//#elide{
//#elide    var s0 := State([Pair(false,false), Pair(false, false), Pair(false, false)]);
//#elide    var s1 := State([Pair(false,false), Pair(true, false), Pair(false, false)]);
//#elide    var s2 := State([Pair(false,false), Pair(true, true), Pair(false, false)]);
//#elide    assert AcquireLeft(c, s0, s1, 1); // witness
//#elide    assert AcquireRight(c, s1, s2, 1); // witness
//#elide    b := [s0, s1, s2];
//#elide}
//#elide
