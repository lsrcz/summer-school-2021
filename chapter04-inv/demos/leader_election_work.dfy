// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: nat) {
    0<=i<|ids|
  }

  predicate UniqueIds() {
    (forall i:nat, j:nat | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
  }

  predicate WF() {
    && 0 < |ids|
    && UniqueIds()
  }
}

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<nat>) {
  predicate WF(k: Constants)
    requires k.WF()
  {
    && |highest_heard| == |k.ids|
  }
}

predicate Init(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
    // Everyone begins having heard about nobody, not even themselves.
  && (forall i:nat | k.ValidIdx(i) :: v.highest_heard[i] == -1)
}

function max(a: nat, b: nat) : nat {
  if a > b then a else b
}

function NextIdx(k: Constants, idx: nat) : nat
  requires k.WF()
  requires k.ValidIdx(idx)
{
  //(idx + 1) % |k.ids|
  if idx+1 == |k.ids| then 0 else idx+1
}

predicate Transmission(k: Constants, v: Variables, v': Variables, src: nat)
{
  && k.WF()
  && v.WF(k)
  && v'.WF(k)
  && k.ValidIdx(src)

  // Neighbor address in ring.
  && var dst := NextIdx(k, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], k.ids[src]);

  // dst only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dst], message);
  // XXX Manos: How could this have been a bug!? How could a src, having sent message X, ever send message Y < X!?

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

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

predicate IsLeader(k: Constants, v: Variables, i: nat)
  requires k.WF()
  requires v.WF(k)
{
  && k.ValidIdx(i)
  && v.highest_heard[i] == k.ids[i]
}

predicate Safety(k: Constants, v: Variables)
  requires k.WF()
  requires v.WF(k)
{
  forall i, j | IsLeader(k, v, i) && IsLeader(k, v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

predicate Between(start:nat, i:nat, end:nat)
{
  if start<end
  then start<i<end
  else i<end || start<i
}

predicate IsChord(k:Constants, v:Variables, start:nat, end:nat)
  requires && k.WF() && v.WF(k)
{
  && k.ValidIdx(start)
  && k.ValidIdx(end)
  && k.ids[start] == v.highest_heard[end]
}

predicate OnChordHeardDominatesId(k:Constants, v:Variables, start:nat, end:nat)
  requires && k.WF() && v.WF(k)
  requires k.ValidIdx(start) && k.ValidIdx(end)
{
  forall i:nat | k.ValidIdx(i) && Between(start, i, end)
    :: v.highest_heard[i] > k.ids[i]
}

predicate OnChordHeardDominatesIdInv(k: Constants, v: Variables)
  requires && k.WF() && v.WF(k)
{
  forall start:nat, end:nat | k.ValidIdx(start) && k.ValidIdx(end) && IsChord(k, v, start, end)
    :: OnChordHeardDominatesId(k, v, start, end)
}

predicate Inv(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
  && OnChordHeardDominatesIdInv(k, v)
  && Safety(k, v)
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
