//#title Single-Server Lock Service Proof
//#desc A more realistic invariant proof of the previous chapter's lock
//#desc service.

// We provide a correct spec for the lock server here, but leave you
// to define the Safety property to be proven.
// You are welcome to prove correct your own model from chapter03,
// but note that may be too hard or too easy if your spec is broken.


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

datatype ServerGrant = Unlocked | Client(id: nat)
datatype ClientRecord = Released | Acquired

datatype Constants = Constants(clientCount: nat) {
  predicate WF() { true }
  predicate ValidIdx(idx: int) {
    0 <= idx < clientCount
  }
}
datatype Variables = Variables(server: ServerGrant, clients: seq<ClientRecord>) {
  predicate WF(c: Constants) {
    |clients| == c.clientCount
  }
}

predicate Init(c:Constants, v:Variables) {
  && v.WF(c)
  && v.server.Unlocked?
  && |v.clients| == c.clientCount
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
}

predicate Acquire(c:Constants, v:Variables, v':Variables, id:int) {
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(id)

  && v.server.Unlocked?

  && v'.server == Client(id)
  && v'.clients == v.clients[id := Acquired]
}

predicate Release(c:Constants, v:Variables, v':Variables, id:int) {
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(id)

  && v.clients[id].Acquired?

  && v'.server.Unlocked?
  && v'.clients == v.clients[id := Released]
}

datatype Step =
  | AcquireStep(id: int)
  | ReleaseStep(id: int)

predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
  match step
    case AcquireStep(id) => Acquire(c, v, v', id)
    case ReleaseStep(id) => Release(c, v, v', id)
}

predicate Next(c:Constants, v:Variables, v':Variables) {
  exists step :: NextStep(c, v, v', step)
}

predicate Safety(c:Constants, v:Variables) {
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
  forall i,j ::
    (&& 0 <= i < |v.clients|
    && 0 <= j < |v.clients|
    && v.clients[i].Acquired?
    && v.clients[j].Acquired?) ==> i == j
}

predicate Inv(c:Constants, v:Variables) {
  if v.server.Unlocked?
  then
    forall i | 0 <= i < |v.clients| :: !v.clients[i].Acquired?
  else
    exists i | 0 <= i < |v.clients| ::
      v.clients[i].Acquired? && (forall j | 0 <= j < |v.clients| && j != i :: !v.clients[j].Acquired?)
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(c:Constants, v:Variables, v':Variables)
  ensures Init(c, v) ==> Inv(c, v)
  ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
  ensures Inv(c, v) ==> Safety(c, v)
{
  if Init(c, v) {
    InitImpliesInv(c, v);
  }
  if Inv(c, v) && Next(c, v, v') {
    NextPreservesInv(c, v, v');
  }
  if Inv(c, v) {
    InvImpliesSafety(c, v);
  }
}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v) {}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  var step :| NextStep(c, v, v', step);
  match step
    case AcquireStep(id) => {
      assert v'.clients[id].Acquired?;
    }
    case ReleaseStep(id) => {
    }
}


lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
}

