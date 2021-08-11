//#instructor The game of Nim. A more advanced state machine than Switch,
//#instructor which also introduces step parameters and the corresponding
//#instructor existentials in the Next() predicate.

datatype Variables = Variables(tokens:int)

predicate Init(v:Variables) {
    v.tokens > 0
}

// Action with parameters
predicate Play(v:Variables, v':Variables, take:int) {
    && 1 <= take <= 4   // Enabling condition
    && take <= v.tokens // Enabling condition
    && v'.tokens == v.tokens - take
}

predicate Next(v:Variables, v':Variables)
{
    exists take :: Play(v, v', take)    // parameters get there-existed in Next
}
