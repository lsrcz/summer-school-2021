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
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
//#exercise  false
//#start-elide
  forall i,j ::
    (&& 0 <= i < |v.clients|
    && 0 <= j < |v.clients|
    && v.clients[i].Acquired?
    && v.clients[j].Acquired?) ==> i == j
//#end-elide
}

//#start-elide
// Safety doesn't care what server thinks, but to get an *inductive* invariant,
// we need to ensure the server doesn't fall out of sync with the clients'
// beliefs.
predicate ServerAgreesClients(v:Variables) {
  v.server.Unlocked? <==> (forall id | 0 <= id < |v.clients| :: v.clients[id].Released?)
}

//#end-elide
predicate Inv(v:Variables) {
//#exercise  true  // probably not strong enough. :v)
//#start-elide
  && Safety(v)
  && ServerAgreesClients(v)
//#end-elide
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(v:Variables, v':Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
//#start-elide
  if Inv(v) && Next(v, v') {
    var step :| NextStep(v, v', step);        // give a variable name ("step") to what happened in Next
    if step.AcquireStep? {                    // case analysis
//      assert !v'.server.Unlocked?;
      assert !v'.clients[step.id].Released?;  // witness to exist (!forall in ServerAgreesClient)
//      assert Inv(v');
//    } else {
//      assert Inv(v');
    }
  }
//#end-elide
}
