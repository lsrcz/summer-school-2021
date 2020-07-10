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

  predicate Safety(s:Variables) {
    // What's a good definition of safety for the lock server? No two clients
    // have the lock simultaneously. Write that here.
    false
  }

  predicate Inv(s:Variables) {
    true  // probably not strong enough. :v)
  }

  // Here's your obligation. Probably easiest to break this up into three
  // lemmas, each P==>Q becomes requires P ensures Q.
  lemma SafetyTheorem(k:Constants, s:Variables, s':Variables)
    ensures Init(k, s) ==> Inv(s)
    ensures Inv(s) && Next(k, s, s') ==> Inv(s')
    ensures Inv(s) ==> Safety(s)
  {
  }
}

