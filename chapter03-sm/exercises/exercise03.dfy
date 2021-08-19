//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

/*
Model a lock service that consists of a single server and an
arbitrary number of clients.

The state of the system includes the server's state (whether the server
knows that some client holds the lock, and if so which one)
and the clients' states (for each client, whether that client knows
it holds the lock).

The system should begin with the server holding the lock.
An acquire step atomically transfers the lock from the server to some client.
(Note that we're not modeling the network yet -- the lock disappears from
the server and appears at a client in a single atomic transition.)
A release step atomically transfers the lock from the client back to the server.

The safety property is that no two clients ever hold the lock
simultaneously.
*/

datatype Constants = Constants(/* You define this ...*/) {
  predicate WF() { true }
}
datatype Variables = Variables(/* You define this ...*/) {
  predicate WF(c: Constants) { true }
}

predicate Init(c:Constants, v:Variables) {
  && v.WF(c)
  && true  // Replace me
}

datatype Step =
  | SomeStep(somearg: int)   // Replace me

predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
  case SomeStep(somearg) => false  // Replace me
}

predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

predicate Safety(c:Constants, v:Variables) {
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
  false
}
