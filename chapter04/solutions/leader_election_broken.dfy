// Each node's identifier (address)
datatype RawConstants = RawConstants(ids: seq<nat>) {
  predicate ValidIdx(i: nat) {
    0<=i<|ids|
  }

  predicate UniqueIds() {
    (forall i, j | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
  }

  predicate WF() {
    && 0 < |k.ids|
    && UniqueIds()
  }
}

//type Constants = rc:RawConstants | rc.WF()
type Constants = RawConstants

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<nat>) {
  predicate WF(k: Constants)
    requires k.WF()
  {
    && |highest_heard| == |k.ids|
  }
}
// type Variables = rv:RawVariables | rv.WF(k) // can't do this because k isn't constant (ha ha)

predicate Init(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
    // Everyone begins having heard about nobody, not even themselves.
  && (forall i | k.ValidIdx(i) :: v.highest_heard[i] == -1)
}

function max(a: nat, b: nat) : nat {
  if a > b then a else b
}

function NextIdx(k: Constants, idx: nat) : nat
  requires k.WF()
  requires ValidIdx(k, idx)
{
  if idx + 1 < |k.ids| then idx + 1 else 0
}

predicate Transmission(k: Constants, v: Variables, v': Variables, src: nat)
{
  && k.WF()
  && v.WF(k)
  && v'.WF(k)
  && 0 <= src < |k.ids|

  // Neighbor address in ring.
  // TODO let's try it with modulo, too.
  && var dst := NextIdx(k, src);
  // Yeah turns out modulo makes dafny stupid.
  // && var dst := (src + 1) % |k.ids|;

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], k.ids[src]);
  && var dst_new_max := max(v.highest_heard[dst], message);
  // Here's bug 1: we compute the max of the message with the highest_heard of dst,
  // and then ignore it.

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
  requires k.WF()
  requires v.WF(k)
{
  && ValidIdx(k, i)
  && v.highest_heard[i] == k.ids[i]
}

// TODO note that the elected leader isn't stable, which isn't ideal.
predicate Safety(k: Constants, v: Variables)
  requires k.WF()
  requires v.WF(k)
{
  forall i, j | IsLeader(k, v, i) && IsLeader(k, v, j) :: i == j
}

predicate IsMaxId(k: Constants, i: nat)
  requires k.WF()
  requires ValidIdx(k, i)
{
  forall j | ValidIdx(k, j) :: k.ids[j] <= k.ids[i]
}

predicate Between(k: Constants, startExclusive: nat, idx: nat, endExclusive: nat)
  requires k.WF()
  requires ValidIdx(k, startExclusive)
  requires ValidIdx(k, idx)
  requires ValidIdx(k, endExclusive)
{
  if startExclusive < endExclusive
  then startExclusive < idx < endExclusive
  else idx < endExclusive || startExclusive < idx
}

// An identifier that has "reached" a distant node some way around the
// ring is at least as high as the id of every node it has passed.
predicate IDOnChordDominatesIDs(k: Constants, v: Variables)
  requires k.WF()
  requires v.WF(k)
{
  forall i, j | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i] == v.highest_heard[j] ::
    forall m | ValidIdx(k, m) && Between(k, i, m, j) :: k.ids[i] > k.ids[m]
}

predicate Inv(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
  && Safety(k, v)
  && IDOnChordDominatesIDs(k, v)
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
