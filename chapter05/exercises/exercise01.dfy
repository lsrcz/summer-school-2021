module Types {
  // TODO finite domain of keys so we can use finite-domained maps and avoid manager nonsense
  type Key(==, !new)

  // Assume a finite domain (set is finite) of possible keys, so we
  // can use (finite) maps. Dafny also offers infinite maps, but those
  // bring another twist, so let's just use what's familiar for now.
  function AllKeys() : set<Key>

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

  function InitialMap() : map<Key, Value>
  {
    map key | key in AllKeys() :: DefaultValue()
  }
}

module MapSpec {
  import opened Types

  datatype Variables = Variables(mapp:map<Key, Value>)

  predicate Init(v_: Variables)
  {
    v_.mapp == InitialMap()
  }

  predicate InsertOp(v_:Variables, v_':Variables, key:Key, value:Value)
  {
    v_'.mapp == v_.mapp[key := value]
  }

  predicate QueryOp(v_:Variables, v_':Variables, key:Key, output:Value)
  {
    && (output == if key in v_.mapp then v_.mapp[key] else DefaultValue())
    && v_' == v_  // no change to map state
  }

  datatype Step =
    | InsertOpStep(key:Key, value:Value)
    | QueryOpStep(key:Key, output:Value)

  predicate NextStep(v_: Variables, v_': Variables, step:Step)
  {
    match step
      case InsertOpStep(key, value) => InsertOp(v_, v_', key, value)
      case QueryOpStep(key, output) => QueryOp(v_, v_', key, output)
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

  datatype Constants = Constants()
  datatype Variables = Variables(mapp:map<Key, Value>)
    // if a key is absent, only the manager can spring it
    // into existence.

  predicate Init(c_: Constants, v_: Variables, hostidx: nat)
  {
    && v_.mapp == if hostidx==0 then InitialMap() else map[]
  }

  predicate Insert(c_: Constants, v_: Variables, v_': Variables, key: Key, value: Value)
  {
    && key in v_.mapp // this host needs to be authoritative on this key
    && v_'.mapp == v_.mapp[key := value]
  }

  predicate Query(c_: Constants, v_: Variables, v_': Variables, key: Key, output: Value)
  {
    && key in v_.mapp
    && output == v_.mapp[key]
    && v_' == v_  // UNCHANGED
  }

  datatype Step =
    | InsertStep(key: Key, value: Value)
    | QueryStep(key: Key, output: Value)

  predicate LocalOpStep(c_: Constants, v_: Variables, v_': Variables, step: Step)
  {
    match step
      case InsertStep(key, value) => Insert(c_, v_, v_', key, value)
      case QueryStep(key, output) => Query(c_, v_, v_', key, output)
  }

  predicate LocalOp(c_: Constants, v_: Variables, v_': Variables)
  {
    exists step :: LocalOpStep(c_, v_, v_', step)
  }

  // A possible enhancement exercise: transfer many key,value pairs in one
  // message.
  datatype Message = TransferKey(key: Key, value: Value)

  // System-partial-actions for message transmission.
  // A matched pair of these happen together atomically, so it's a
  // "synchronous" message delivery model. (We'll add more realism later.)
  predicate Send(c_: Constants, v_: Variables, v_': Variables, msg: Message)
  {
    && msg.key in v_.mapp // can only give away what I'mapp authoritative for
    && v_.mapp[msg.key] == msg.value  // transmit the correct value
    && v_'.mapp == map key | key in v_.mapp && key!=msg.key :: v_.mapp[key] // forget this key
  }

  predicate Receive(c_: Constants, v_: Variables, v_': Variables, msg: Message)
  {
    && v_'.mapp == v_.mapp[msg.key := msg.value]  // learn the new key,value pair.
  }
}

module System {
  import Host

  datatype Constants = Constants(hosts: seq<Host.Constants>)
  {
    predicate WF() { 0 < |hosts| }
    predicate ValidHost(hostidx: nat) { hostidx < |hosts| }
  }

  datatype Variables = Variables(hosts: seq<Host.Variables>)
  {
    predicate WF(c_: Constants) { |hosts| == |c_.hosts| }
  }
  
  predicate Init(c_: Constants, v_: Variables)
  {
    && c_.WF()
    && v_.WF(c_)
    && (forall hostidx:nat | c_.ValidHost(hostidx) :: Host.Init(c_.hosts[hostidx], v_.hosts[hostidx], hostidx))
  }

  predicate LocalOp(c_: Constants, v_: Variables, v_': Variables, hostidx: nat)
  {
    && v_.WF(c_)
    && v_'.WF(c_)
    && c_.ValidHost(hostidx)
    && Host.LocalOp(c_.hosts[hostidx], v_.hosts[hostidx], v_'.hosts[hostidx])
    // all other host state UNCHANGED
    && (forall otherhost:nat | c_.ValidHost(otherhost) && otherhost!=hostidx :: v_'.hosts[otherhost] == v_.hosts[otherhost])
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
    && (forall otherhost:nat | c_.ValidHost(otherhost) && otherhost!=src && otherhost!=dst
        :: v_'.hosts[otherhost] == v_.hosts[otherhost])
  }

  datatype Step =
    | LocalOpStep(hostidx:nat)
    | TransmitOpStep(src:nat, dst:nat, message:Host.Message)

  predicate NextStep(c_: Constants, v_: Variables, v_': Variables, step:Step)
  {
    match step
      case LocalOpStep(hostidx) => LocalOp(c_, v_, v_', hostidx)
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

  predicate HostHasKey(c_: Constants, v_: Variables, hostidx:nat, key:Key)
    requires v_.WF(c_)
  {
    && c_.ValidHost(hostidx)
    && key in v_.hosts[hostidx].mapp
  }

  // Pulling the choose out into its own function is sometimes necessary due
  // to a (deliberate) stupidity in Dafny: it doesn't treat :| expressions
  // as subsitution-equivalent, even though the are (as evidenced by pulling
  // one into a function).
  function TheHostWithKey(c_: Constants, v_: Variables, key:Key) : nat
    requires v_.WF(c_)
    requires exists hostidx :: HostHasKey(c_, v_, hostidx, key);
  {
    var hostidx:nat :| HostHasKey(c_, v_, hostidx, key);
    hostidx
  }


  function AbstractionOneKey(c_: Constants, v_: Variables, key:Key) : Value
    requires v_.WF(c_)
  {
    if exists idx :: HostHasKey(c_, v_, idx, key)
    then
      v_.hosts[TheHostWithKey(c_, v_, key)].mapp[key]
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
    if count==0 then {} else AllKeysRecurse(c_, v_, count-1) + v_.hosts[count-1].mapp.Keys
  }

  function AllKeys(c_: Constants, v_: Variables) : set<Key>
    requires v_.WF(c_)
  {
    AllKeysRecurse(c_, v_, |c_.hosts|)
  }

  function Abstraction(c_: Constants, v_: Variables) : MapSpec.Variables
    requires v_.WF(c_)
  {
    MapSpec.Variables(map key | key in AllKeys(c_, v_) :: AbstractionOneKey(c_, v_, key))
  }

  predicate Inv(c_: Constants, v_: Variables)
  {
    && c_.WF()
    && v_.WF(c_)
    // No two distinct hosts have the same key.
    && (forall key, hostidx:nat, otherhost:nat
        | && c_.ValidHost(hostidx) && c_.ValidHost(otherhost)
          && key in v_.hosts[hostidx].mapp && key in v_.hosts[otherhost].mapp
        :: hostidx == otherhost
      )
  }

  lemma InitAllKeysEmpty(c_: Constants, v_: Variables, count: nat)
    requires Init(c_, v_)
    requires 0 < count <= |c_.hosts|
    ensures AllKeysRecurse(c_, v_, count) == InitialMap().Keys
  {
    if count==1 {
      assert AllKeysRecurse(c_, v_, count) == v_.hosts[0].mapp.Keys == InitialMap().Keys;
    } else {
      InitAllKeysEmpty(c_, v_, count-1);
    }
    
  }

  lemma AllKeysMembership(c_: Constants, v_: Variables, count: nat)
    requires Inv(c_, v_)
    requires count <= |c_.hosts|
    ensures forall key ::
      (key in AllKeysRecurse(c_, v_, count) <==> exists hostidx:nat :: hostidx<count && key in v_.hosts[hostidx].mapp)
  {
  }

  lemma InitRefines(c_: Constants, v_: Variables)
    requires Init(c_, v_)
    ensures MapSpec.Init(Abstraction(c_, v_))
    ensures Inv(c_, v_)
  {
    InitAllKeysEmpty(c_, v_, |c_.hosts|);
    AllKeysMembership(c_, v_, |c_.hosts|);
  }

  lemma InsertPreservesInvAndRefines(c_: Constants, v_: Variables, v_': Variables, insertHost: nat, insertedKey: Key, value: Value)
    requires Inv(c_, v_)
    requires Next(c_, v_, v_')
    requires c_.ValidHost(insertHost)
    requires (forall otherhost:nat | c_.ValidHost(otherhost) && otherhost!=insertHost :: v_'.hosts[otherhost] == v_.hosts[otherhost]);
    requires Host.Insert(c_.hosts[insertHost], v_.hosts[insertHost], v_'.hosts[insertHost], insertedKey, value)
    ensures Inv(c_, v_')
    ensures MapSpec.Next(Abstraction(c_, v_), Abstraction(c_, v_'))
  {
    var abstractMap := Abstraction(c_, v_).mapp;
    var abstractMap' := Abstraction(c_, v_').mapp;

    forall key
      ensures key in abstractMap' <==> key in abstractMap || key == insertedKey // domain
      ensures key in abstractMap' ==> (abstractMap'[key] == if key==insertedKey then value else abstractMap[key])  // value
    {
      AllKeysMembership(c_, v_', |c_.hosts|);
      // Narrowing the calls to AllKeysMembership(v_) helps z3 save 15s!
      // (But domain proof can be replaced with just AllKeysMembership(v_);AllKeysMembership(v_') and it'll still work.)
      if key == insertedKey {
      } else if key in abstractMap' {
        assert key in abstractMap by { AllKeysMembership(c_, v_, |c_.hosts|); }
      } else if key in abstractMap {
        assert key in abstractMap' by { AllKeysMembership(c_, v_, |c_.hosts|); }
      }

      if key in abstractMap' {
        if key==insertedKey {
          assert HostHasKey(c_, v_', insertHost, key);  // trigger
          assert AbstractionOneKey(c_, v_', key) == value; // trigger
        } else {
          var ihost:nat :| ihost<|c_.hosts| && key in v_'.hosts[ihost].mapp;
          assert forall otherhost | c_.ValidHost(otherhost) && otherhost!=ihost :: !HostHasKey(c_, v_, otherhost, key);  // trigger
          assert HostHasKey(c_, v_', ihost, key) by { AllKeysMembership(c_, v_, |c_.hosts|); }
          assert TheHostWithKey(c_, v_', key) == ihost; // witness
          assert abstractMap'[key] == abstractMap[key]; // trigger  // TODO unstable?
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
          case InsertStep(key, value) => InsertPreservesInvAndRefines(c_, v_, v_', idx, key, value);
          case QueryStep(key, output) => {
            assert Inv(c_, v_');
            assert v_ == v_'; // weirdly obvious trigger
            assert Abstraction(c_, v_) == Abstraction(c_, v_');
            assert output == Abstraction(c_, v_).mapp[key];
            assert MapSpec.QueryOp(Abstraction(c_, v_), Abstraction(c_, v_'), key, output);
            assert MapSpec.NextStep(Abstraction(c_, v_), Abstraction(c_, v_'), MapSpec.QueryOpStep(key, output));
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
