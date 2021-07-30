// TODO !!! move this to chapter 7 because it's about refinement

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

  predicate Init(v: Variables)
  {
    v.mapp == InitialMap()
  }

  predicate InsertOp(v:Variables, v':Variables, key:Key, value:Value)
  {
    && key in AllKeys()
    && v'.mapp == v.mapp[key := value]
  }

  predicate QueryOp(v:Variables, v':Variables, key:Key, output:Value)
  {
    && key in AllKeys()
    && (output == if key in v.mapp then v.mapp[key] else DefaultValue())
    && v' == v  // no change to map state
  }

  datatype Step =
    | InsertOpStep(key:Key, value:Value)
    | QueryOpStep(key:Key, output:Value)

  predicate NextStep(v: Variables, v': Variables, step:Step)
  {
    match step
      case InsertOpStep(key, value) => InsertOp(v, v', key, value)
      case QueryOpStep(key, output) => QueryOp(v, v', key, output)
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }
}

// A "synchronous" KV store (network messages are delivered
// instantaneously).

module Implementation {
  import opened Types

  type HostIdx = nat

  datatype Constants = Constants(mapCount: nat)
  {
    predicate WF() { 0 < mapCount }
    predicate ValidHost(idx: HostIdx) { idx < mapCount }
  }

  datatype Variables = Variables(maps:seq<map<Key, Value>>)
  {
    predicate WF(c: Constants) { |maps| == c.mapCount }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall idx:HostIdx | c.ValidHost(idx) :: v.maps[idx] == if idx==0 then InitialMap() else map[])
  }

  predicate Insert(c: Constants, v: Variables, v': Variables, idx: HostIdx, key: Key, value: Value)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    && v'.maps == v.maps[idx := v.maps[idx][key := value]]
  }

  predicate Query(c: Constants, v: Variables, v': Variables, idx: HostIdx, key: Key, output: Value)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    && output == v.maps[idx][key]
    && v' == v  // UNCHANGED
  }

  function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j != key :: m[j];
    assert m'.Keys == m.Keys - {key};
    m'
  }

  // A possible enhancement exercise: transfer many key,value pairs in one step
  predicate Transfer(c: Constants, v: Variables, v': Variables, sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(sendIdx)
    && c.ValidHost(recvIdx)
    && key in v.maps[sendIdx]
    && v'.maps[sendIdx] == MapRemoveOne(v.maps[sendIdx], key)  // key leaves sending map
    && v'.maps[recvIdx] == v.maps[recvIdx][key := value]    // key appears in recv map
    && (forall otherIdx:HostIdx | c.ValidHost(otherIdx) && otherIdx != sendIdx && otherIdx != recvIdx
        :: v'.maps[otherIdx] == v.maps[otherIdx]) // unchanged other participants
  }

  datatype Step =
    | InsertStep(idx: HostIdx, key: Key, value: Value)
    | QueryStep(idx: HostIdx, key: Key, output: Value)
    | TransferStep(sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    match step
      case InsertStep(idx, key, value) => Insert(c, v, v', idx, key, value)
      case QueryStep(idx, key, output) => Query(c, v, v', idx, key, output)
      case TransferStep(sendIdx, recvIdx, key, value) => Transfer(c, v, v', sendIdx, recvIdx, key, value)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

module RefinementProof {
  import opened Types
  import MapSpec
  import opened Implementation

  predicate HostHasKey(c: Constants, v: Variables, hostidx:HostIdx, key:Key)
    requires v.WF(c)
  {
    && c.ValidHost(hostidx)
    && key in v.maps[hostidx]
  }

  // Pulling the choose out into its own function is sometimes necessary due
  // to a (deliberate) stupidity in Dafny: it doesn't treat :| expressions
  // as subsitution-equivalent, even though the are (as evidenced by pulling
  // one into a function).
  function TheHostWithKey(c: Constants, v: Variables, key:Key) : HostIdx
    requires v.WF(c)
    requires exists hostidx :: HostHasKey(c, v, hostidx, key);
  {
    var hostidx:HostIdx :| HostHasKey(c, v, hostidx, key);
    hostidx
  }


  function AbstractionOneKey(c: Constants, v: Variables, key:Key) : Value
    requires v.WF(c)
  {
    if exists idx :: HostHasKey(c, v, idx, key)
    then
      v.maps[TheHostWithKey(c, v, key)][key]
    else DefaultValue()
  }

  // We construct the finite set of possible map keys here, all
  // because we need to supply Dafny with simple evidence that our map domain
  // is finite for the map comprehension in Abstraction().
  // (An alternative would be to switch to imaps -- maps with potentially-infinite
  // domains -- but that would require making the spec fancier. This was a compromise.)

  // put into library
  function DropLast<T>(theSeq: seq<T>) : seq<T>
    requires 0 < |theSeq|
  {
    theSeq[..|theSeq|-1]
  }

  function Last<T>(theSeq: seq<T>) : T
    requires 0 < |theSeq|
  {
    theSeq[|theSeq|-1]
  }

  function UnionSeqOfSets<T>(theSets: seq<set<T>>) : set<T>
  {
    if |theSets| == 0 then {} else
      UnionSeqOfSets(DropLast(theSets)) + Last(theSets)
  }

  function KnownKeys(c: Constants, v: Variables) : set<Key>
    requires v.WF(c)
  {
    UnionSeqOfSets(seq(c.mapCount, i requires 0<=i<c.mapCount => v.maps[i].Keys))
  }

  // Packaged as lemma. Proves trivially as ensures of KnownKeys,
  // but creates a trigger storm.
  lemma HostKeysSubsetOfKnownKeys(c: Constants, v: Variables, count: nat)
    requires v.WF(c)
    requires count <= c.mapCount
    ensures forall idx | 0 <= idx < count :: v.maps[idx].Keys <= KnownKeys(c, v)
  {
  }

  function Abstraction(c: Constants, v: Variables) : MapSpec.Variables
    requires v.WF(c)
  {
    MapSpec.Variables(map key | key in KnownKeys(c, v) :: AbstractionOneKey(c, v, key))
  }

  // This does slow things down quite a bit.
  predicate {:opaque} KeysHeldUniquely(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall key, hostidx:HostIdx, otherhost:HostIdx
        | && c.ValidHost(hostidx) && c.ValidHost(otherhost)
          && key in v.maps[hostidx] && key in v.maps[otherhost]
        :: hostidx == otherhost
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    // Every key lives somewhere.
    && KnownKeys(c, v) == Types.AllKeys()
    // No key lives in two places.
    && KeysHeldUniquely(c, v)
  }

  lemma InitAllKeysEmpty(c: Constants, v: Variables, count: nat)
    requires Init(c, v)
    requires 0 < count <= c.mapCount
    ensures KnownKeys(c, v) == AllKeys()
  {
    forall key | key in KnownKeys(c, v) ensures key in AllKeys() {
      var idx :| key in v.maps[idx].Keys;
      assert v.maps[idx].Keys <= AllKeys();
      assert key in AllKeys();
    }
    forall key | key in AllKeys() ensures key in KnownKeys(c, v) {
      assert key in v.maps[0].Keys;
      assert v.maps[0].Keys <= KnownKeys(c, v);
    }
  }

  lemma AllKeysMembership(c: Constants, v: Variables, count: nat)
    requires Inv(c, v)
    requires count <= c.mapCount
    ensures forall key ::
      (key in KnownKeys(c, v) <==> exists hostidx:HostIdx :: hostidx<count && key in v.maps[hostidx])
  {
  }

  lemma InitRefines(c: Constants, v: Variables)
    requires c.WF()
    requires Init(c, v)
    ensures MapSpec.Init(Abstraction(c, v))
    ensures Inv(c, v)
  {
    InitAllKeysEmpty(c, v, c.mapCount);
    reveal_KeysHeldUniquely();
  }

  lemma InsertPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, insertHost: HostIdx, insertedKey: Key, value: Value)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(insertHost)
    requires (forall otherhost:HostIdx | c.ValidHost(otherhost) && otherhost!=insertHost :: v'.maps[otherhost] == v.maps[otherhost]);
    requires Insert(c, v, v', insertHost, insertedKey, value)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    var abstractMap := Abstraction(c, v).mapp;
    var abstractMap' := Abstraction(c, v').mapp;

    forall key
      ensures key in abstractMap' <==> key in abstractMap || key == insertedKey // domain
      ensures key in abstractMap' ==> (abstractMap'[key] == if key==insertedKey then value else abstractMap[key])  // value
    {
      if key == insertedKey {
        assert key in v'.maps[insertHost];
        assert v'.maps[insertHost].Keys <= abstractMap'.Keys;
        assert key in abstractMap';
      }
      if key in abstractMap {
        assert key in abstractMap';
      }
      if key in abstractMap' {
        if key != insertedKey {
          assert key in abstractMap;
        }

  //      AllKeysMembership(c, v', c.mapCount);
        // Narrowing the calls to AllKeysMembership(v) helps z3 save 15s!
        // (But domain proof can be replaced with just AllKeysMembership(v);AllKeysMembership(v') and it'll still work.)
        if key == insertedKey {
        } else if key in abstractMap' {
          assert key in abstractMap by { AllKeysMembership(c, v, c.mapCount); }
        } else if key in abstractMap {
          assert key in abstractMap' by { AllKeysMembership(c, v, c.mapCount); }
        }

        if key in abstractMap' {
          if key==insertedKey {
            assert HostHasKey(c, v', insertHost, key);  // trigger
            assert AbstractionOneKey(c, v', key) == value; // trigger
          } else {
            var ihost:HostIdx :| ihost<c.mapCount && key in v'.maps[ihost];
            assert forall otherhost | c.ValidHost(otherhost) && otherhost!=ihost :: !HostHasKey(c, v, otherhost, key);  // trigger
            assert HostHasKey(c, v', ihost, key) by { AllKeysMembership(c, v, c.mapCount); }
            assert TheHostWithKey(c, v', key) == ihost; // witness
            assert abstractMap'[key] == abstractMap[key]; // trigger  // TODO unstable?
          }
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
      case InsertStep(idx, key, value) => {
        InsertPreservesInvAndRefines(c, v, v', idx, key, value);
      }
      case QueryStep(idx, key, output) => {
        assert v == v'; // weirdly obvious trigger
        assert Inv(c, v') by { reveal_KeysHeldUniquely(); }
        assert key in KnownKeys(c, v) by { HostKeysSubsetOfKnownKeys(c, v, c.mapCount); }
        assert output == Abstraction(c, v).mapp[key] by {
          assert HostHasKey(c, v, idx, key);  // witness
          reveal_KeysHeldUniquely();
        }
        assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.QueryOpStep(key, output)); // witness
      }
      case TransferStep(sendIdx, recvIdx, key, value) => {
        assume false;
      }
  }
}
