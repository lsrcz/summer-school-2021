module LockServer {

  datatype Option<V> = None | Some(value:V)
  function NumClients() : int ensures NumClients() > 0
  newtype ClientId = b: int | 0 <= b < NumClients()
  type ClientMap = m: map<ClientId, bool> | forall c :: c in m
    witness map k:ClientId | true :: false

  datatype Constants = Constants()
  datatype Variables = Variables(holder:Option<ClientId>, clientHolds:ClientMap)

  predicate Init(k:Constants, s:Variables) {
    && s.holder.None?
    && forall c :: !s.clientHolds[c]
  }

  predicate Grant(k:Constants, s:Variables, s':Variables, toClient:ClientId) {
    && s.holder.None?
    && s'.holder == Some(toClient)  // Omitted for proof debug trap
    && s'.clientHolds == s.clientHolds[toClient := true]
  }

  predicate Return(k:Constants, s:Variables, s':Variables, fromClient:ClientId) {
    && s.holder == Some(fromClient)
    && s'.holder.None?
    && s'.clientHolds == s.clientHolds[fromClient := false]
  }

  datatype Step = GrantStep(toClient:ClientId) | ReturnStep(fromClient:ClientId)

  predicate NextStep(k:Constants, s:Variables, s':Variables, step:Step) {
    match step {
      case GrantStep(toClient) => Grant(k, s, s', toClient)
      case ReturnStep(fromClient) => Grant(k, s, s', fromClient)
    }
  }

  predicate Next(k:Constants, s:Variables, s':Variables) {
    exists step :: NextStep(k, s, s', step)
  }
}

module LockServerProof {
  import opened LockServer

  predicate Safety(k:Constants, s:Variables) {
    forall c1, c2 :: s.clientHolds[c1] && s.clientHolds[c2] ==> c1 == c2
  }
  
  predicate ServerExcludesClients(k:Constants, s:Variables) {
    s.holder.None? ==> (forall c :: !s.clientHolds[c])
  }

  predicate Inv(k:Constants, s:Variables) {
    && Safety(k, s)
    && ServerExcludesClients(k, s)
  }

  lemma InvInit(k:Constants, s:Variables, s':Variables)
    requires Init(k, s)
    ensures Inv(k, s)
  {
  }

  lemma InvNext(k:Constants, s:Variables, s':Variables)
    requires Next(k, s, s')
    requires Inv(k, s)
    ensures Inv(k, s')
  {
  }

  lemma InvImpliesSafety(k:Constants, s:Variables)
    requires Inv(k, s)
    ensures Safety(k, s)
  {
  }
}
