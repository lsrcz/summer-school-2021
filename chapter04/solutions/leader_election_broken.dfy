// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>)

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<nat>)

predicate ValidIdx(k: Constants, i: nat) {
  0<=i<|k.ids|
}

predicate UniqueIds(k: Constants) {
  (forall i, j | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i]==k.ids[j] :: i == j)
}

predicate WF(k: Constants, s: Variables) {
  && 0 < |k.ids|
  && UniqueIds(k)
  && |s.highest_heard| == |k.ids|
}

predicate Init(k: Constants, s: Variables)
{
  && WF(k, s)
    // Everyone begins having heard about nobody, not even themselves.
  && (forall i | ValidIdx(k, i) :: s.highest_heard[i] == -1)
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
  // TODO let's try it with modulo, too.
  && var dst := NextIdx(k, src);
  // Yeah turns out modulo makes dafny stupid.
  // && var dst := (src + 1) % |k.ids|;

  // src sends the max of its highest_heard value and its own id.
  && var message := max(s.highest_heard[src], k.ids[src]);
  && var dst_new_max := max(s.highest_heard[dst], message);
  // Here's bug 1: we compute the max of the message with the highest_heard of dst,
  // and then ignore it.

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

// TODO note that the elected leader isn't stable, which isn't ideal.
predicate Safety(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i, j | IsLeader(k, s, i) && IsLeader(k, s, j) :: i == j
}

predicate IsMaxId(k: Constants, i: nat)
  requires ValidIdx(k, i)
{
  forall j | ValidIdx(k, j) :: k.ids[j] <= k.ids[i]
}

predicate Between(k: Constants, startExclusive: nat, idx: nat, endExclusive: nat)
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
predicate IDOnChordDominatesIDs(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i, j | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i] == s.highest_heard[j] ::
    forall m | ValidIdx(k, m) && Between(k, i, m, j) :: k.ids[i] > k.ids[m]
}

predicate Inv(k: Constants, s: Variables)
{
  && WF(k, s)
  && Safety(k, s)
  && IDOnChordDominatesIDs(k, s)
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
