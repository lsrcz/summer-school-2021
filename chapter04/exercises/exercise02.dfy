datatype ServerGrant = Unlocked | Client(id: nat)

datatype ClientRecord = Released | Acquired

datatype Variables = Variables(server: ServerGrant, clients: seq<ClientRecord>)

predicate Init(v: Variables) {
  && v.server.Unlocked?
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
}

predicate Acquire(v: Variables, v':Variables, id:int) {
  && 0 <= id < |v.clients|

  // Enabling condition: The server checks its local state.
  && v.server.Unlocked?

  // Update the server state.
  && v'.server == Client(id)

  // Update the client that acquired.
  && |v'.clients| == |v.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |v.clients| ::
      v'.clients[i] == if i == id then Acquired else v.clients[i] )
}

predicate Release(v: Variables, v':Variables, id:int) {
  && 0 <= id < |v.clients|

  // Enabling condition: The client trying to release checks its local state.
  && v.clients[id].Acquired?

  // Update the server state.
  && v'.server.Unlocked?

  // Update the client that released.
  && |v'.clients| == |v.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |v.clients| ::
      v'.clients[i] == if i == id then Released else v.clients[i] )
}

datatype Step = AcquireStep(id:int) | ReleaseStep(id:int)

predicate NextStep(v:Variables, v':Variables, step:Step) {
  match step {
    case AcquireStep(toClient) => Acquire(v, v', toClient)
    case ReleaseStep(fromClient) => Release(v, v', fromClient)
  }
}

predicate Next(v:Variables, v':Variables) {
  exists step :: NextStep(v, v', step)
}

predicate Safety(v:Variables) {
  // What'v a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
  false
}

predicate Inv(v:Variables) {
  true  // probably not strong enough. :v)
}

// Here'v your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(v:Variables, v':Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
}
