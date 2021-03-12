//#instructor 
//#instructor 
//#instructor Relative to the coke machine, the students need to
//#instructor write their own datatype for philosophers and pair
//#instructor (or equivalent concepts)
//#instructor Introduces the constants idiom.
//#instructor 


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

predicate Next(c:Constants, s:State, s':State) {
//#elide    exists pi:nat :: 
//#elide    (|| AcquireLeft(c, s, s', pi)
//#elide     || AcquireRight(c, s, s', pi)
//#elide     || ReleaseBoth(c, s, s', pi))
}

// here is the safety property
predicate ForkConsistency(c:Constants, s:State) 
{
    && WellFormed(c, s)
    && (forall i | 0 <= i < c.tableSize :: !(
        && s.philosophers[i].right 
        && s.philosophers[PhilosopherToTheRightOf(c,i)].left
        ))
}

// here is a proof of the safety property. This lemma should verify
// without adding a body 
lemma ForkConsistencyLemma() 
    ensures forall c, s | Init(c,s) :: ForkConsistency(c, s)
    ensures forall c, s, s' | ForkConsistency(c, s) && Next(c, s, s') :: ForkConsistency(c, s')
{
}

// this predicate and the following lemma are a way to prevent trivial
// specifications of the problem that would prevent a philosopher from
// having both forks
predicate PhilosopherHasBothForks(c:Constants, s:State, pi:nat)
    requires pi < c.tableSize
    requires WellFormed(c, s)
{
    && s.philosophers[pi].left
    && s.philosophers[pi].right
}

lemma PseudoLiveness(c:Constants, pi:nat) returns (b:seq<State>)
    requires c.tableSize == 3
    requires pi == 1
    ensures 0 < |b| 
    ensures Init(c, b[0])
    ensures forall i | 0 <= i < |b|-1 :: Next(c, b[i], b[i+1])
    ensures WellFormed(c, b[|b|-1])
    ensures PhilosopherHasBothForks(c, b[|b|-1], pi)
{
    var s0 := State([Pair(false,false), Pair(false, false), Pair(false, false)]);
    var s1 := State([Pair(false,false), Pair(true, false), Pair(false, false)]);
    var s2 := State([Pair(false,false), Pair(true, true), Pair(false, false)]);
    assert AcquireLeft(c, s0, s1, 1); // witness
    assert AcquireRight(c, s1, s2, 1); // witness
    b := [s0, s1, s2];
}

