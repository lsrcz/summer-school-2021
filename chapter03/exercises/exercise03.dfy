// Single-Server Lock Service

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

datatype Constants = Constants(/* You define this ...*/)
datatype State = State(/* You define this ...*/)

predicate Init(s:State) {
  true  // Replace me
}

predicate Next(s:State, s':State) {
  true  // Replace me
}

predicate Safety(s:State) {
  true  // Change me to the important property!
}
