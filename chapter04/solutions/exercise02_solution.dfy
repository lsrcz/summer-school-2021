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
  forall i,j ::
    (&& 0 <= i < |s.clients|
    && 0 <= j < |s.clients|
    && s.clients[i].Acquired?
    && s.clients[j].Acquired?) ==> i == j
}

// Safety doesn't care what server thinks, but to get an *inductive* invariant,
// we need to ensure the server doesn't fall out of sync with the clients'
// beliefs.
predicate ServerAgreesClients(s:State) {
  s.server.Unlocked? <==> (forall id | 0 <= id < |s.clients| :: s.clients[id].Released?)
}

predicate Inv(s:State) {
  && Safety(s)
  && ServerAgreesClients(s)
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(s:State, s':State)
  ensures Init(s) ==> Inv(s)
  ensures Inv(s) && Next(s, s') ==> Inv(s')
  ensures Inv(s) ==> Safety(s)
{
  if Inv(s) && Next(s, s') {
    var step :| NextStep(s, s', step);        // give a variable name ("step") to what happened in Next
    if step.AcquireStep? {                    // case analysis
//      assert !s'.server.Unlocked?;
      assert !s'.clients[step.id].Released?;  // witness to exist (!forall in ServerAgreesClient)
//      assert Inv(s');
//    } else {
//      assert Inv(s');
    }
  }
}
