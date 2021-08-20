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
datatype Variables = Variables(acquired: seq<bool>)

// An initial predicate to define well-formed constants.
// Feel free to add more if you need them
predicate WellFormedConstants(c:Constants) {
    && 0 < c.tableSize
}


// An initial predicate to define well-formed state.
// Feel free to add to this predicate, if necessary
predicate WellFormed(c:Constants, v:Variables) {
    && WellFormedConstants(c)
    && c.tableSize == |v.acquired|
}

predicate Init(c:Constants, v:Variables) {
    && WellFormed(c, v)
    && forall a | a in v.acquired :: !a
}

function LeftChopstickIndex(c: Constants, pi: nat): nat {
    pi
}

function RightChopstickIndex(c: Constants, pi: nat): nat {
    if pi == c.tableSize - 1 then 0 else pi + 1
}

predicate AcquireSingle(c: Constants, v: Variables, v': Variables, pi: nat) {
    && WellFormed(c, v)
    && WellFormed(c, v')
    && 0 <= pi < c.tableSize
    && forall p | 0 <= p < c.tableSize && p != pi :: v.acquired[p] == v'.acquired[p]
    && !v.acquired[pi]
    && v'.acquired[pi]
}

// Philosopher with index pi acquires left chopstick
predicate AcquireLeft(c:Constants, v:Variables, v':Variables, pi:nat) {
    AcquireSingle(c, v, v', LeftChopstickIndex(c, pi))
}

// Philosopher with index pi acquires right chopstick
predicate AcquireRight(c:Constants, v:Variables, v':Variables, pi:nat) {
    && AcquireSingle(c, v, v', RightChopstickIndex(c, pi))
}

// Philosopher with index pi releases both chopsticks
predicate ReleaseBoth(c:Constants, v:Variables, v':Variables, pi:nat) {
    var leftIdx := LeftChopstickIndex(c, pi);
    var rightIdx := RightChopstickIndex(c, pi);
    && WellFormed(c, v)
    && WellFormed(c, v')
    && 0 <= pi < c.tableSize
    && forall p | 0 <= p < c.tableSize && p != leftIdx && p != rightIdx ::
         v.acquired[p] == v'.acquired[p]
    && v.acquired[leftIdx]
    && v.acquired[rightIdx]
    && !v'.acquired[leftIdx]
    && !v'.acquired[rightIdx]
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

