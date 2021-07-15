// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>)

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<nat>)

predicate ValidIdx(k: Constants, i: nat) {
  0<=i<|k.ids|
}

predicate UniqueIDs(k: Constants) {
  // No two nodes have the same identifier.
  && (forall i:nat, j:nat | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i]==k.ids[j]
    :: i == j)
}

predicate WF(k: Constants, v: Variables) {
  && 0 < |k.ids|
  && |v.highest_heard| == |k.ids|
  && UniqueIDs(k)
}

predicate Init(k: Constants, v: Variables)
{
  && WF(k, v)
    // Everyone begins having heard about nobody, not even themselves.
  && (forall i:nat | ValidIdx(k, i) :: v.highest_heard[i] == -1)
}

function max(a: nat, b: nat) : nat {
  if a > b then a else b
}

function NextIdx(k: Constants, idx: nat) : nat
  requires ValidIdx(k, idx)
{
  if idx + 1 < |k.ids| then idx + 1 else 0
}

predicate Transmission(k: Constants, v: Variables, v': Variables, src: nat)
{

  && WF(k, v)
  && WF(k, v')
  && 0 <= src < |k.ids|

  // Neighbor address in ring.
  && var dst := NextIdx(k, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], k.ids[src]);
  && var dst_new_max := max(v.highest_heard[dst], message);

  && v' == v.(highest_heard := v.highest_heard[dst := dst_new_max])
}

datatype Step = TransmissionStep(src: nat)

predicate NextStep(k: Constants, v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(src) => Transmission(k, v, v', src)
  }
}

predicate Next(k: Constants, v: Variables, v': Variables)
{
  exists step :: NextStep(k, v, v', step)
}

predicate IsLeader(k: Constants, v: Variables, i: nat)
  requires WF(k, v)
{
  && ValidIdx(k, i)
  && v.highest_heard[i] == k.ids[i]
}

predicate Safety(k: Constants, v: Variables)
  requires WF(k, v)
{
  forall i, j | IsLeader(k, v, i) && IsLeader(k, v, j) :: i == j
}

predicate IsMaxId(k: Constants, id: nat)
{
  forall j:nat | ValidIdx(k, j) :: k.ids[j] <= id
}

predicate InvPred(k: Constants, v: Variables)
  requires WF(k, v)
{
  forall i:nat | ValidIdx(k, i) && !IsMaxId(k, k.ids[i]) :: !IsLeader(k, v, i)
}

predicate HighestHeardDominatesID(k: Constants, v: Variables)
  requires WF(k, v)
{
  forall i:nat | ValidIdx(k, i) && v.highest_heard[i] != -1 :: v.highest_heard[i] >= k.ids[i]
}

predicate Inv(k: Constants, v: Variables)
{
  && WF(k, v)
  && InvPred(k, v)
  && HighestHeardDominatesID(k, v)
}

lemma InitImpliesInv(k: Constants, v: Variables)
  requires Init(k, v)
  ensures Inv(k, v)
{
}

lemma NextPreservesInv(k: Constants, v: Variables, v': Variables)
  requires Inv(k, v)
  requires Next(k, v, v')
  ensures Inv(k, v')
{
}

lemma InvImpliesSafety(k: Constants, v: Variables)
  requires Inv(k, v)
  ensures Safety(k, v)
{
}
