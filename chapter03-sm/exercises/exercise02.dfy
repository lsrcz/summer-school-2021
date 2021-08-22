//#title Dining Philosophers
//#desc A more challenging state machine: define the state datatype.

// Define the state machine for the Dining Philosophers.
// There are N philosophers sitting around a round table.
// Between every pair of philosophers lies a chopstick.
// Every philosopher has three possible actions:
//  * Acquire the chopstick to their left.
//  * Acquire the chopstick to their right.
//  * Release both chopsticks (in a single step).

datatype Constants = Constants(tableSize:nat)

//Use this datatype to define all the relevant state
datatype Pair = Pair(left: bool, right: bool)
datatype Variables = Variables(philosophers: seq<Pair>)

// An initial predicate to define well-formed constants.
// Feel free to add more if you need them
predicate WellFormedConstants(c:Constants) {
    && 0 < c.tableSize
}


// An initial predicate to define well-formed state.
// Feel free to add to this predicate, if necessary
predicate WellFormed(c:Constants, v:Variables) {
    && WellFormedConstants(c)
    && c.tableSize == |v.philosophers|
}

predicate Init(c:Constants, v:Variables) {
    && WellFormed(c, v)
    && forall i | 0 <= i < c.tableSize :: v.philosophers[i] == Pair(false, false)
}

function LeftPhilosopher(c: Constants, pi: nat): nat
  requires WellFormedConstants(c) {
    if pi == 0 then c.tableSize - 1 else pi - 1
}

function RightPhilosopher(c: Constants, pi: nat) : nat 
{
    if pi == c.tableSize - 1 then 0 else pi + 1
}

// Philosopher with index pi acquires left chopstick
predicate AcquireLeft(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].left)
    && !(v.philosophers[LeftPhilosopher(c, pi)].right)
    && v' == v.(philosophers := v.philosophers[pi := v.philosophers[pi].(left := true)])
}

// Philosopher with index pi acquires right chopstick
predicate AcquireRight(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && !(v.philosophers[pi].right)
    && !(v.philosophers[RightPhilosopher(c, pi)].left)
    && v' == v.(philosophers := v.philosophers[pi := v.philosophers[pi].(right := true)])
}

// Philosopher with index pi releases both chopsticks
predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, pi:nat) {
    && WellFormed(c, v)
    && pi < c.tableSize
    && v.philosophers[pi].left
    && v.philosophers[pi].right
    && v' == v.(philosophers := v.philosophers[pi := Pair(false, false)])
}

datatype Step =
    | AcquireLeftStep(pi: nat)
    | AcquireRightStep(pi: nat)
    | ReleaseBothStep(pi: nat)

predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step) {
    match step
        case AcquireLeftStep(pi) => AcquireLeft(c, v, v', pi)
        case AcquireRightStep(pi) => AcquireRight(c, v, v', pi)
        case ReleaseBothStep(pi) => ReleaseBoth(c, v, v', pi)
}

predicate Next(c:Constants, v:Variables, v':Variables) {
    exists step :: NextStep(c, v, v', step)
}

predicate ForkConsistency(c: Constants, v: Variables) {
    && WellFormed(c, v)
    && (forall i | 0 <= i < c.tableSize :: !(
        && v.philosophers[i].right
        && v.philosophers[RightPhilosopher(c, i)].left
    ))
}

lemma ForkConsistencyLemma()
    ensures forall c, v | Init(c, v) :: ForkConsistency(c, v)
    ensures forall c, v, v' | ForkConsistency(c, v) && Next(c, v, v') :: ForkConsistency(c, v') {

    }
