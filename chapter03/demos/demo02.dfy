//#instructor The game of Nim. A more advanced state machine than Switch,
//#instructor which also introduces step parameters and the corresponding
//#instructor existentials in the Next() predicate.

datatype State = State(tokens:int)

predicate Init(s:State) {
    s.tokens > 0
}

// Action with parameters
predicate Play(s:State, s':State, take:int) {
    && 1 <= take <= 4   // Enabling condition
    && take <= s.tokens // Enabling condition
    && s'.tokens == s.tokens - take
}

predicate Next(s:State, s':State)
{
    exists take :: Play(s, s', take)    // parameters get there-existed in Next
}
