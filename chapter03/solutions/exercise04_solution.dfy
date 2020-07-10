datatype ServerGrant = Unlocked | Client(id: nat)

datatype ClientRecord = Released | Acquired

datatype State = State(server: ServerGrant, clients: seq<ClientRecord>)

predicate Init(s: State) {
  && s.server.Unlocked?
  && forall i | 0 <= i < |s.clients| :: s.clients[i].Released?
}

predicate Acquire(s: State, s':State, id:int) {
  && 0 <= id < |s.clients|
  && s.server.Unlocked?
  && s'.server == Client(id)
  && |s'.clients| == |s.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |s.clients| ::
      s'.clients[i] == if i == id then Acquired else Released )
}

predicate Release(s: State, s':State, id:int) {
  && 0 <= id < |s.clients|
  && s.clients[id].Acquired?
  && s'.server.Unlocked?
  && |s'.clients| == |s.clients|  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |s.clients| :: s'.clients[i].Released? )
}

predicate Next(s: State, s':State, id:int) {
  || ( exists id :: Acquire(s, s', id) )
  || ( exists id :: Release(s, s', id) )
}
