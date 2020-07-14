datatype ServerGrant = Unlocked | Client(id: nat)

datatype ClientRecord = Released | Acquired

datatype State = State(server: ServerGrant, clients: seq<ClientRecord>)

predicate Init(s: State) {
  && s.server.Unlocked?
  && forall i | 0 <= i < |s.clients| :: s.clients[i].Released?
}

predicate Acquire(s: State, s':State, id:int) {
  && 0 <= id < |s.clients|

  // Enabling condition: The server checks its local state.
  && s.server.Unlocked?

  // Update the server state.
  && s'.server == Client(id)

  // Update the client that acquired.
  && |s'.clients| == |s.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |s.clients| ::
      s'.clients[i] == if i == id then Acquired else s.clients[i] )
}

predicate Release(s: State, s':State, id:int) {
  && 0 <= id < |s.clients|

  // Enabling condition: The client trying to release checks its local state.
  && s.clients[id].Acquired?

  // Update the server state.
  && s'.server.Unlocked?

  // Update the client that released.
  && |s'.clients| == |s.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |s.clients| ::
      s'.clients[i] == if i == id then Released else s.clients[i] )
}

datatype Step = AcquireStep(id:int) | ReleaseStep(id:int)

predicate NextStep(s:State, s':State, step:Step) {
  match step {
    case AcquireStep(toClient) => Acquire(s, s', toClient)
    case ReleaseStep(fromClient) => Release(s, s', fromClient)
  }
}

predicate Next(s:State, s':State) {
  exists step :: NextStep(s, s', step)
}

predicate Safety(s:State) {
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
  false
}

predicate Inv(s:State) {
  true  // probably not strong enough. :v)
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(s:State, s':State)
  ensures Init(s) ==> Inv(s)
  ensures Inv(s) && Next(s, s') ==> Inv(s')
  ensures Inv(s) ==> Safety(s)
{
}
