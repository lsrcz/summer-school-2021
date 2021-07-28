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

  predicate Init(v: Variables)
  {
    v.m == map[]
  }

  predicate InsertOp(v:Variables, v':Variables, k:Key, value:Value)
  {
    v'.m == v.m[k := value]
  }

  predicate QueryOp(v:Variables, v':Variables, k:Key, output:Value)
  {
    && (output == if k in v.m then v.m[k] else DefaultValue())
    && v' == v  // no change to map state
  }

  datatype Step =
    | InsertOpStep(k:Key, value:Value)
    | QueryOpStep(k:Key, output:Value)

  predicate NextStep(v: Variables, v': Variables, step:Step)
  {
    match step
      case InsertOpStep(k, value) => InsertOp(v, v', k, value)
      case QueryOpStep(k, output) => QueryOp(v, v', k, output)
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
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

  predicate Init(c: Constants, v: Variables, i: nat)
  {
    && c.manager == (i==0)
    && v.m == map[]
  }

  predicate Insert(c: Constants, v: Variables, v': Variables, k: Key, value: Value)
  {
    && k in v.m // this host needs to be authoritative on this key
    && v'.m == v.m[k := value]
  }

  predicate Query(c: Constants, v: Variables, v': Variables, k: Key, output: Value)
  {
    && k in v.m
    && output == v.m[k]
    && v' == v  // UNCHANGED
  }

  // This is how we allow other hosts to serve queries for missing
  // keys: we insert an explicit value to get the key into our map.
  predicate FillDefault(c: Constants, v: Variables, v': Variables, k: Key)
  {
    && c.manager  // only manager is authoritative on missing keys
    && k !in v.m
    && v'.m == v.m[k := DefaultValue()]
  }

  datatype Step =
    | InsertStep(k: Key, value: Value)
    | QueryStep(k: Key, output: Value)
    | FillDefaultStep(k: Key)

  predicate LocalOpStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    match step
      case InsertStep(key, value) => Insert(c, v, v', key, value)
      case QueryStep(key, output) => Query(c, v, v', key, output)
      case FillDefaultStep(key) => FillDefault(c, v, v', key)
  }

  predicate LocalOp(c: Constants, v: Variables, v': Variables)
  {
    exists step :: LocalOpStep(c, v, v', step)
  }

  datatype Message = TransferKey(k: Key, value: Value)

  // System-partial-actions for message transmission.
  // A matched pair of these happen together atomically, so it's a
  // "synchronous" message delivery model. (We'll add more realism later.)
  predicate Send(c: Constants, v: Variables, v': Variables, msg: Message)
  {
    && msg.k in v.m // can only give away what Abstraction'm authoritative for
    && v.m[msg.k] == msg.value  // transmit the correct value
    && v'.m == map k | k in v.m && k!=msg.k :: v.m[k] // forget this key
  }

  predicate Receive(c: Constants, v: Variables, v': Variables, msg: Message)
  {
    && v'.m == v.m[msg.k := msg.value]  // learn the new key,value pair.
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
    predicate WF(c: Constants) { |hosts| == |c.hosts| }
  }
  
  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall i:nat | c.ValidHost(i) :: Host.Init(c.hosts[i], v.hosts[i], i))
  }

  predicate LocalOp(c: Constants, v: Variables, v': Variables, i: nat)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(i)
    && Host.LocalOp(c.hosts[i], v.hosts[i], v'.hosts[i])
    // all other host state UNCHANGED
    && (forall j:nat | c.ValidHost(j) && j!=i :: v'.hosts[j] == v.hosts[j])
  }

  predicate TransmitOp(c: Constants, v: Variables, v': Variables, src: nat, dst: nat, message: Host.Message)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(src)
    && c.ValidHost(dst)
    && Host.Send(c.hosts[src], v.hosts[src], v'.hosts[src], message)
    && Host.Receive(c.hosts[dst], v.hosts[dst], v'.hosts[dst], message)
    // all other host state UNCHANGED
    && (forall j:nat | c.ValidHost(j) && j!=src && j!=dst
        :: v'.hosts[j] == v.hosts[j])
  }

  datatype Step =
    | LocalOpStep(i:nat)
    | TransmitOpStep(src:nat, dst:nat, message:Host.Message)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step:Step)
  {
    match step
      case LocalOpStep(i) => LocalOp(c, v, v', i)
      case TransmitOpStep(src, dst, message) => TransmitOp(c, v, v', src, dst, message)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

module RefinementProof {
  import opened Types
  import MapSpec
  import opened System

  predicate HostHasKey(c: Constants, v: Variables, i:nat, k:Key)
    requires v.WF(c)
  {
    && c.ValidHost(i)
    && k in v.hosts[i].m
  }

  // Pulling the choose out into its own function is sometimes necessary due
  // to a (deliberate) stupidity in Dafny: it doesn't treat :| expressions
  // as subsitution-equivalent, even though the are (as evidenced by pulling
  // one into a function).
  function TheHostWithKey(c: Constants, v: Variables, k:Key) : nat
    requires v.WF(c)
    requires exists i :: HostHasKey(c, v, i, k);
  {
    var i:nat :| HostHasKey(c, v, i, k);
    i
  }


  function Ikey(c: Constants, v: Variables, key:Key) : Value
    requires v.WF(c)
  {
    if exists idx :: HostHasKey(c, v, idx, key)
    then
      v.hosts[TheHostWithKey(c, v, key)].m[key]
    else DefaultValue()
  }

  // We recursively construct the finite set of possible map keys here, all
  // because we need to supply Dafny with simple evidence that our map domain
  // is finite for the map comprehension in Abstraction().
  // (An alternative would be to switch to imaps -- maps with potentially-infinite
  // domains -- but that would require making the spec fancier. This was a compromise.)
  function AllKeysRecurse(c: Constants, v: Variables, count: nat) : set<Key>
    requires v.WF(c)
    requires count <= |c.hosts|
  {
    if count==0 then {} else AllKeysRecurse(c, v, count-1) + v.hosts[count-1].m.Keys
  }

  function AllKeys(c: Constants, v: Variables) : set<Key>
    requires v.WF(c)
  {
    AllKeysRecurse(c, v, |c.hosts|)
  }

  function Abstraction(c: Constants, v: Variables) : MapSpec.Variables
    requires v.WF(c)
  {
    MapSpec.Variables(map k | k in AllKeys(c, v) :: Ikey(c, v, k))
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    // No two distinct hosts have the same key.
    && (forall k, i:nat, j:nat
        | && c.ValidHost(i) && c.ValidHost(j)
          && k in v.hosts[i].m && k in v.hosts[j].m
        :: i == j
      )
  }

//  lemma InitAllKeysEmpty(c: Constants, v: Variables, count: nat)
//    requires Init(c, v)
//    requires count <= |c.hosts|
//    ensures AllKeysRecurse(c, v, count) == {}
//  {
//  }
//
  lemma AllKeysMembership(c: Constants, v: Variables, count: nat)
    requires Inv(c, v)
    requires count <= |c.hosts|
    ensures forall k ::
      (k in AllKeysRecurse(c, v, count) <==> exists i:nat :: i<count && k in v.hosts[i].m)
  {
  }

  lemma InitRefines(c: Constants, v: Variables)
    requires Init(c, v)
    ensures MapSpec.Init(Abstraction(c, v))
    ensures Inv(c, v)
  {
   // InitAllKeysEmpty(c, v, |c.hosts|);
    AllKeysMembership(c, v, |c.hosts|);
  }

  lemma InsertPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, insertHost: nat, insertedKey: Key, value: Value)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(insertHost)
    requires (forall j:nat | c.ValidHost(j) && j!=insertHost :: v'.hosts[j] == v.hosts[j]);
    requires Host.Insert(c.hosts[insertHost], v.hosts[insertHost], v'.hosts[insertHost], insertedKey, value)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    var im := Abstraction(c, v).m;
    var im' := Abstraction(c, v').m;

    forall k
      ensures k in im' <==> k in im || k == insertedKey // domain
      ensures k in im' ==> (im'[k] == if k==insertedKey then value else im[k])  // value
    {
      AllKeysMembership(c, v', |c.hosts|);
      // Narrowing the calls to AllKeysMembership(v) helps z3 save 15s!
      // (But domain proof can be replaced with just AllKeysMembership(v);AllKeysMembership(v') and it'll still work.)
      if k == insertedKey {
      } else if k in im' {
        assert k in im by { AllKeysMembership(c, v, |c.hosts|); }
      } else if k in im {
        assert k in im' by { AllKeysMembership(c, v, |c.hosts|); }
      }

      if k in im' {
        if k==insertedKey {
          assert HostHasKey(c, v', insertHost, k);  // trigger
          assert Ikey(c, v', k) == value; // trigger
        } else {
          var ihost:nat :| ihost<|c.hosts| && k in v'.hosts[ihost].m;
          assert forall j | c.ValidHost(j) && j!=ihost :: !HostHasKey(c, v, j, k);  // trigger
          assert HostHasKey(c, v', ihost, k) by { AllKeysMembership(c, v, |c.hosts|); }
          assert TheHostWithKey(c, v', k) == ihost; // witness
          assert im'[k] == im[k]; // trigger
        }
      }
    }

    assert MapSpec.InsertOp(Abstraction(c, v), Abstraction(c, v'), insertedKey, value); // bizarre magic backwards causality-violating trigger
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.InsertOpStep(insertedKey, value)); // witness
  }

  lemma NextPreservesInvAndRefines(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    var step :| NextStep(c, v, v', step);
    match step
      case LocalOpStep(idx) => {
        var hstep :| Host.LocalOpStep(c.hosts[idx], v.hosts[idx], v'.hosts[idx], hstep);
        match hstep
          case InsertStep(k, value) => InsertPreservesInvAndRefines(c, v, v', idx, k, value);
          case QueryStep(k, output) => {
            assume false;
            assert Inv(c, v');
            assert Abstraction(c, v) == Abstraction(c, v');
            assert MapSpec.Next(Abstraction(c, v), Abstraction(c, v'));
          }
          case FillDefaultStep(k) => {
            assume false;
            assert Inv(c, v');
            assert Abstraction(c, v) == Abstraction(c, v');
            assert MapSpec.Next(Abstraction(c, v), Abstraction(c, v'));
          }
      }
      case TransmitOpStep(src, dst, message) => {
        assume false;
        assert Inv(c, v');
        assert Abstraction(c, v) == Abstraction(c, v');
        assert MapSpec.Next(Abstraction(c, v), Abstraction(c, v'));
      }
  }
}
