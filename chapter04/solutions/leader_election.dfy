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

predicate WF(k: Constants, s: Variables) {
  && 0 < |k.ids|
  && |s.highest_heard| == |k.ids|
  && UniqueIDs(k)
}

predicate Init(k: Constants, s: Variables)
{
  && WF(k, s)
    // Everyone begins having heard about nobody, not even themselves.
  && (forall i:nat | ValidIdx(k, i) :: s.highest_heard[i] == -1)
}

function max(a: nat, b: nat) : nat {
  if a > b then a else b
}

function NextIdx(k: Constants, idx: nat) : nat
  requires ValidIdx(k, idx)
{
  if idx + 1 < |k.ids| then idx + 1 else 0
}

predicate Transmission(k: Constants, s: Variables, s': Variables, src: nat)
{

  && WF(k, s)
  && WF(k, s')
  && 0 <= src < |k.ids|

  // Neighbor address in ring.
  && var dst := NextIdx(k, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(s.highest_heard[src], k.ids[src]);
  && var dst_new_max := max(s.highest_heard[dst], message);

  && s' == s.(highest_heard := s.highest_heard[dst := dst_new_max])
}

datatype Step = TransmissionStep(src: nat)

predicate NextStep(k: Constants, s: Variables, s': Variables, step: Step)
{
  match step {
    case TransmissionStep(src) => Transmission(k, s, s', src)
  }
}

predicate Next(k: Constants, s: Variables, s': Variables)
{
  exists step :: NextStep(k, s, s', step)
}

predicate IsLeader(k: Constants, s: Variables, i: nat)
  requires WF(k, s)
{
  && ValidIdx(k, i)
  && s.highest_heard[i] == k.ids[i]
}

predicate Safety(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i, j | IsLeader(k, s, i) && IsLeader(k, s, j) :: i == j
}

predicate IsMaxId(k: Constants, id: nat)
{
  forall j:nat | ValidIdx(k, j) :: k.ids[j] <= id
}

predicate InvPred(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i:nat | ValidIdx(k, i) && !IsMaxId(k, k.ids[i]) :: !IsLeader(k, s, i)
}

predicate HighestHeardDominatesID(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i:nat | ValidIdx(k, i) && s.highest_heard[i] != -1 :: s.highest_heard[i] >= k.ids[i]
}

predicate Inv(k: Constants, s: Variables)
{
  && WF(k, s)
  && InvPred(k, s)
  && HighestHeardDominatesID(k, s)
}

lemma InitImpliesInv(k: Constants, s: Variables)
  requires Init(k, s)
  ensures Inv(k, s)
{
}

lemma NextPreservesInv(k: Constants, s: Variables, s': Variables)
  requires Inv(k, s)
  requires Next(k, s, s')
  ensures Inv(k, s')
{
}

lemma InvImpliesSafety(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures Safety(k, s)
{
}
