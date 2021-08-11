datatype ServerGrant = Unlocked | Client(id: nat)

datatype ClientRecord = Released | Acquired

datatype Variables = Variables(server: ServerGrant, clients: seq<ClientRecord>)

predicate Init(v: Variables) {
  && v.server.Unlocked?
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
}

predicate Acquire(v: Variables, v':Variables, id:int) {
  && 0 <= id < |v.clients|
  && v.server.Unlocked?
  && v'.server == Client(id)
  && |v'.clients| == |v.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |v.clients| ::
      v'.clients[i] == if i == id then Acquired else v.clients[i] )
}

predicate Release(v: Variables, v':Variables, id:int) {
  && 0 <= id < |v.clients|
  && v.clients[id].Acquired?
  && v'.server.Unlocked?
  && |v'.clients| == |v.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |v.clients| ::
      v'.clients[i] == if i == id then Released else v.clients[i] )
}

predicate Next(v: Variables, v':Variables) {
  || ( exists id :: Acquire(v, v', id) )
  || ( exists id :: Release(v, v', id) )
}
