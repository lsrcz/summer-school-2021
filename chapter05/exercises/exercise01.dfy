module Types {
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
      case InsertStep(k, value) => Insert(c, v, v', k, value)
      case QueryStep(k, output) => Query(c, v, v', k, output)
      case FillDefaultStep(k) => FillDefault(c, v, v', k)
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
    && msg.k in v.m // can only give away what I'm authoritative for
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

  function Ik(c: Constants, v: Variables, k:Key) : Value
    requires v.WF(c)
  {
    if exists i :: HostHasKey(c, v, i, k)
    then
      var i:nat :| HostHasKey(c, v, i, k);
      v.hosts[i].m[k]
    else DefaultValue()
  }

  function I(c: Constants, v: Variables) : MapSpec.Variables
    requires v.WF(c)
  {
    MapSpec.Variables(map k | true :: Ik(c, v, k))
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

  lemma InitRefines(c: Constants, v: Variables)
    requires Init(c, v)
    ensures MapSpec.Init(I(c, v))
    ensures Inv(c, v)
  {
  }

  lemma NextPreservesInvAndRefines(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
    ensures MapSpec.Next(I(c, v), I(c, v'))
  {
  }
}
