module Types {
  // TODO finite domain of keys so we can use finite-domained maps and avoid manager nonsense
  type Key(==, !new)
  type Value(==, !new)
    // (==) means whatever this type is, it has equality defined on it.
    // !new means this type can't be allocated on the heap; it's a mathematical
    // immutable object.
    // Since we're in math-land, not implementation-land, we always want both features
    // of all types, so we declare them on these otherwise-unspecified types.
    // Missing == gives "map domain type must support equality" errors.
    // Missing !new gives "...not allowed to depend on the set of allocated references" errors.

  function DefaultValue() : Value
    // No body -> this is an axiom.
}

module MapSpec {
  import opened Types

  datatype Variables = Variables(m:map<Key, Value>)

  predicate Init(v_: Variables)
  {
    v_.m == map[]
  }

  predicate InsertOp(v_:Variables, v_':Variables, k:Key, value:Value)
  {
    v_'.m == v_.m[k := value]
  }

  predicate QueryOp(v_:Variables, v_':Variables, k:Key, output:Value)
  {
    && (output == if k in v_.m then v_.m[k] else DefaultValue())
    && v_' == v_  // no change to map state
  }

  datatype Step =
    | InsertOpStep(k:Key, value:Value)
    | QueryOpStep(k:Key, output:Value)

  predicate NextStep(v_: Variables, v_': Variables, step:Step)
  {
    match step
      case InsertOpStep(k, value) => InsertOp(v_, v_', k, value)
      case QueryOpStep(k, output) => QueryOp(v_, v_', k, output)
  }

  predicate Next(v_: Variables, v_': Variables)
  {
    exists step :: NextStep(v_, v_', step)
  }
}

// A "synchronous" KV store (network messages are delivered
// instantaneously).

module Host {
  import opened Types

  datatype Constants = Constants(manager: bool)
  datatype Variables = Variables(m:map<Key, Value>)
    // if a key is absent, only the manager can spring it
    // into existence.

  predicate Init(c_: Constants, v_: Variables, i: nat)
  {
    && c_.manager == (i==0)
    && v_.m == map[]
  }

  predicate Insert(c_: Constants, v_: Variables, v_': Variables, k: Key, value: Value)
  {
    && k in v_.m // this host needs to be authoritative on this key
    && v_'.m == v_.m[k := value]
  }

  predicate Query(c_: Constants, v_: Variables, v_': Variables, k: Key, output: Value)
  {
    && k in v_.m
    && output == v_.m[k]
    && v_' == v_  // UNCHANGED
  }

  // This is how we allow other hosts to serve queries for missing
  // keys: we insert an explicit value to get the key into our map.
  predicate FillDefault(c_: Constants, v_: Variables, v_': Variables, k: Key)
  {
    && c_.manager  // only manager is authoritative on missing keys
    && k !in v_.m
    && v_'.m == v_.m[k := DefaultValue()]
  }

  datatype Step =
    | InsertStep(k: Key, value: Value)
    | QueryStep(k: Key, output: Value)
    | FillDefaultStep(k: Key)

  predicate LocalOpStep(c_: Constants, v_: Variables, v_': Variables, step: Step)
  {
    match step
      case InsertStep(key, value) => Insert(c_, v_, v_', key, value)
      case QueryStep(key, output) => Query(c_, v_, v_', key, output)
      case FillDefaultStep(key) => FillDefault(c_, v_, v_', key)
  }

  predicate LocalOp(c_: Constants, v_: Variables, v_': Variables)
  {
    exists step :: LocalOpStep(c_, v_, v_', step)
  }

  datatype Message = TransferKey(k: Key, value: Value)

  // System-partial-actions for message transmission.
  // A matched pair of these happen together atomically, so it's a
  // "synchronous" message delivery model. (We'll add more realism later.)
  predicate Send(c_: Constants, v_: Variables, v_': Variables, msg: Message)
  {
    && msg.k in v_.m // can only give away what I'm authoritative for
    && v_.m[msg.k] == msg.value  // transmit the correct value
    && v_'.m == map k | k in v_.m && k!=msg.k :: v_.m[k] // forget this key
  }

  predicate Receive(c_: Constants, v_: Variables, v_': Variables, msg: Message)
  {
    && v_'.m == v_.m[msg.k := msg.value]  // learn the new key,value pair.
  }
}

module System {
  import Host

  datatype Constants = Constants(hosts: seq<Host.Constants>)
  {
    predicate ValidHost(i: nat) { i < |hosts| }
  }

  datatype Variables = Variables(hosts: seq<Host.Variables>)
  {
    predicate WF(c_: Constants) { |hosts| == |c_.hosts| }
  }
  
  predicate Init(c_: Constants, v_: Variables)
  {
    && v_.WF(c_)
    && (forall i:nat | c_.ValidHost(i) :: Host.Init(c_.hosts[i], v_.hosts[i], i))
  }

  predicate LocalOp(c_: Constants, v_: Variables, v_': Variables, i: nat)
  {
    && v_.WF(c_)
    && v_'.WF(c_)
    && c_.ValidHost(i)
    && Host.LocalOp(c_.hosts[i], v_.hosts[i], v_'.hosts[i])
    // all other host state UNCHANGED
    && (forall j:nat | c_.ValidHost(j) && j!=i :: v_'.hosts[j] == v_.hosts[j])
  }

  predicate TransmitOp(c_: Constants, v_: Variables, v_': Variables, src: nat, dst: nat, message: Host.Message)
  {
    && v_.WF(c_)
    && v_'.WF(c_)
    && c_.ValidHost(src)
    && c_.ValidHost(dst)
    && Host.Send(c_.hosts[src], v_.hosts[src], v_'.hosts[src], message)
    && Host.Receive(c_.hosts[dst], v_.hosts[dst], v_'.hosts[dst], message)
    // all other host state UNCHANGED
    && (forall j:nat | c_.ValidHost(j) && j!=src && j!=dst
        :: v_'.hosts[j] == v_.hosts[j])
  }

  datatype Step =
    | LocalOpStep(i:nat)
    | TransmitOpStep(src:nat, dst:nat, message:Host.Message)

  predicate NextStep(c_: Constants, v_: Variables, v_': Variables, step:Step)
  {
    match step
      case LocalOpStep(i) => LocalOp(c_, v_, v_', i)
      case TransmitOpStep(src, dst, message) => TransmitOp(c_, v_, v_', src, dst, message)
  }

  predicate Next(c_: Constants, v_: Variables, v_': Variables)
  {
    exists step :: NextStep(c_, v_, v_', step)
  }
}

module RefinementProof {
  import opened Types
  import MapSpec
  import opened System

  predicate HostHasKey(c_: Constants, v_: Variables, i:nat, k:Key)
    requires v_.WF(c_)
  {
    && c_.ValidHost(i)
    && k in v_.hosts[i].m
  }

  // Pulling the choose out into its own function is sometimes necessary due
  // to a (deliberate) stupidity in Dafny: it doesn't treat :| expressions
  // as subsitution-equivalent, even though the are (as evidenced by pulling
  // one into a function).
  function TheHostWithKey(c_: Constants, v_: Variables, k:Key) : nat
    requires v_.WF(c_)
    requires exists i :: HostHasKey(c_, v_, i, k);
  {
    var i:nat :| HostHasKey(c_, v_, i, k);
    i
  }


  function Ikey(c_: Constants, v_: Variables, key:Key) : Value
    requires v_.WF(c_)
  {
    if exists idx :: HostHasKey(c_, v_, idx, key)
    then
      v_.hosts[TheHostWithKey(c_, v_, key)].m[key]
    else DefaultValue()
  }

  // We recursively construct the finite set of possible map keys here, all
  // because we need to supply Dafny with simple evidence that our map domain
  // is finite for the map comprehension in Abstraction().
  // (An alternative would be to switch to imaps -- maps with potentially-infinite
  // domains -- but that would require making the spec fancier. This was a compromise.)
  function AllKeysRecurse(c_: Constants, v_: Variables, count: nat) : set<Key>
    requires v_.WF(c_)
    requires count <= |c_.hosts|
  {
    if count==0 then {} else AllKeysRecurse(c_, v_, count-1) + v_.hosts[count-1].m.Keys
  }

  function AllKeys(c_: Constants, v_: Variables) : set<Key>
    requires v_.WF(c_)
  {
    AllKeysRecurse(c_, v_, |c_.hosts|)
  }

  function Abstraction(c_: Constants, v_: Variables) : MapSpec.Variables
    requires v_.WF(c_)
  {
    MapSpec.Variables(map k | k in AllKeys(c_, v_) :: Ikey(c_, v_, k))
  }

  predicate Inv(c_: Constants, v_: Variables)
  {
    && v_.WF(c_)
    // No two distinct hosts have the same key.
    && (forall k, i:nat, j:nat
        | && c_.ValidHost(i) && c_.ValidHost(j)
          && k in v_.hosts[i].m && k in v_.hosts[j].m
        :: i == j
      )
  }

//  lemma InitAllKeysEmpty(c_: Constants, v_: Variables, count: nat)
//    requires Init(c_, v_)
//    requires count <= |c_.hosts|
//    ensures AllKeysRecurse(c_, v_, count) == {}
//  {
//  }
//
  lemma AllKeysMembership(c_: Constants, v_: Variables, count: nat)
    requires Inv(c_, v_)
    requires count <= |c_.hosts|
    ensures forall k ::
      (k in AllKeysRecurse(c_, v_, count) <==> exists i:nat :: i<count && k in v_.hosts[i].m)
  {
  }

  lemma InitRefines(c_: Constants, v_: Variables)
    requires Init(c_, v_)
    ensures MapSpec.Init(Abstraction(c_, v_))
    ensures Inv(c_, v_)
  {
   // InitAllKeysEmpty(c_, v_, |c_.hosts|);
    AllKeysMembership(c_, v_, |c_.hosts|);
  }

  lemma InsertPreservesInvAndRefines(c_: Constants, v_: Variables, v_': Variables, insertHost: nat, insertedKey: Key, value: Value)
    requires Inv(c_, v_)
    requires Next(c_, v_, v_')
    requires c_.ValidHost(insertHost)
    requires (forall j:nat | c_.ValidHost(j) && j!=insertHost :: v_'.hosts[j] == v_.hosts[j]);
    requires Host.Insert(c_.hosts[insertHost], v_.hosts[insertHost], v_'.hosts[insertHost], insertedKey, value)
    ensures Inv(c_, v_')
    ensures MapSpec.Next(Abstraction(c_, v_), Abstraction(c_, v_'))
  {
    var im := Abstraction(c_, v_).m;
    var im' := Abstraction(c_, v_').m;

    forall k
      ensures k in im' <==> k in im || k == insertedKey // domain
      ensures k in im' ==> (im'[k] == if k==insertedKey then value else im[k])  // value
    {
      AllKeysMembership(c_, v_', |c_.hosts|);
      // Narrowing the calls to AllKeysMembership(v_) helps z3 save 15s!
      // (But domain proof can be replaced with just AllKeysMembership(v_);AllKeysMembership(v_') and it'll still work.)
      if k == insertedKey {
      } else if k in im' {
        assert k in im by { AllKeysMembership(c_, v_, |c_.hosts|); }
      } else if k in im {
        assert k in im' by { AllKeysMembership(c_, v_, |c_.hosts|); }
      }

      if k in im' {
        if k==insertedKey {
          assert HostHasKey(c_, v_', insertHost, k);  // trigger
          assert Ikey(c_, v_', k) == value; // trigger
        } else {
          var ihost:nat :| ihost<|c_.hosts| && k in v_'.hosts[ihost].m;
          assert forall j | c_.ValidHost(j) && j!=ihost :: !HostHasKey(c_, v_, j, k);  // trigger
          assert HostHasKey(c_, v_', ihost, k) by { AllKeysMembership(c_, v_, |c_.hosts|); }
          assert TheHostWithKey(c_, v_', k) == ihost; // witness
          assert im'[k] == im[k]; // trigger
        }
      }
    }

    assert MapSpec.InsertOp(Abstraction(c_, v_), Abstraction(c_, v_'), insertedKey, value); // bizarre magic backwards causality-violating trigger
    assert MapSpec.NextStep(Abstraction(c_, v_), Abstraction(c_, v_'), MapSpec.InsertOpStep(insertedKey, value)); // witness
  }

  lemma NextPreservesInvAndRefines(c_: Constants, v_: Variables, v_': Variables)
    requires Inv(c_, v_)
    requires Next(c_, v_, v_')
    ensures Inv(c_, v_')
    ensures MapSpec.Next(Abstraction(c_, v_), Abstraction(c_, v_'))
  {
    var step :| NextStep(c_, v_, v_', step);
    match step
      case LocalOpStep(idx) => {
        var hstep :| Host.LocalOpStep(c_.hosts[idx], v_.hosts[idx], v_'.hosts[idx], hstep);
        match hstep
          case InsertStep(k, value) => InsertPreservesInvAndRefines(c_, v_, v_', idx, k, value);
          case QueryStep(k, output) => {
            assume false;
            assert Inv(c_, v_');
            assert Abstraction(c_, v_) == Abstraction(c_, v_');
            assert MapSpec.Next(Abstraction(c_, v_), Abstraction(c_, v_'));
          }
          case FillDefaultStep(k) => {
            assume false;
            assert Inv(c_, v_');
            assert Abstraction(c_, v_) == Abstraction(c_, v_');
            assert MapSpec.Next(Abstraction(c_, v_), Abstraction(c_, v_'));
          }
      }
      case TransmitOpStep(src, dst, message) => {
        assume false;
        assert Inv(c_, v_');
        assert Abstraction(c_, v_) == Abstraction(c_, v_');
        assert MapSpec.Next(Abstraction(c_, v_), Abstraction(c_, v_'));
      }
  }
}
