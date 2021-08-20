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

datatype ServerState = Unlocked | LockedBy(client: nat)
datatype ClientState = Client(acquired: bool)
datatype Constants = Constants(numOfClient: nat)
datatype Variables = Variables(serverState: ServerState, clientState: seq<ClientState>)

predicate WellFormed(c: Constants, v: Variables) {
  && c.numOfClient == |v.clientState|
}

predicate Unlocked(c: Constants, v: Variables) {
  && v.serverState.Unlocked?
  && forall client | 0 <= client < |v.clientState| :: !v.clientState[client].acquired
}

predicate AcquiredBy(c: Constants, v: Variables, client: nat) {
  && 0 <= client < |v.clientState|
  && v.serverState.LockedBy?
  && v.serverState.client == client
  && forall client1 | 0 <= client1 < |v.clientState| && client != client1 :: !v.clientState[client1].acquired
  && v.clientState[client].acquired
}

predicate Init(c:Constants, v:Variables) {
  && WellFormed(c, v)
  && Unlocked(c, v)
}

predicate Lock(c: Constants, v: Variables, v': Variables, client: nat) {
  && WellFormed(c, v)
  && Unlocked(c, v)
  && |v.clientState| == |v'.clientState|
  && AcquiredBy(c, v', client)
}

predicate Release(c: Constants, v: Variables, v': Variables, client: nat) {
  && WellFormed(c, v)
  && AcquiredBy(c, v, client)
  && |v.clientState| == |v'.clientState|
  && Unlocked(c, v')
}

datatype Step =
    | LockStep(client: nat)
    | ReleaseStep(client: nat)

predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step) {
    match step
        case LockStep(client) => Lock(c, v, v', client)
        case ReleaseStep(client) => Release(c, v, v', client)
}

predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step: Step :: NextStep(c, v, v', step)
}

predicate Safety(c:Constants, v:Variables) {
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
  WellFormed(c, v) && forall c1, c2 | 0 <= c1 < c.numOfClient && 0 <= c2 < c.numOfClient ::
    (v.clientState[c1].acquired && v.clientState[c2].acquired) ==> c1 == c2
}

predicate Inv(c: Constants, v: Variables) {
  Safety(c, v)
}

lemma SafetyProof()
  ensures forall c, v | Init(c, v) :: Inv(c, v)
  ensures forall c, v, v' | Inv(c, v) && Next(c, v, v') :: Inv(c, v')
  ensures forall c, v | Inv(c, v) :: Safety(c, v)
{
  /*
  forall c, v, v' | Inv(c, v) && Next(c, v, v') ensures Inv(c, v') {
    InductiveStep(c, v, v');
  }
  */
}

/*
lemma InductiveStep(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
}
*/
