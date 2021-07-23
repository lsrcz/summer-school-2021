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
  && k.UniqueIds()
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
  if idx + 1 == |k.ids| then 0 else idx + 1
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

// // accounting for wrap
// // start, end exclusive.
// predicate Between(start: nat, i: nat, end: nat)
// {
//   if start<end
//   then start<i<end
//   else i<end || start<i
// }
// 
// predicate IsChord(k: Constants, v: Variables, start: nat, end: nat)
// {
//   && k.WF()
//   && v.WF(k)
//   && k.ValidIdx(start)
//   && k.ValidIdx(end)
//   && k.ids[start] == v.highest_heard[end]
// }
// 
// predicate OnChordHeardDominatesId(k: Constants, v: Variables, start: nat, end: nat)
//   requires k.WF()
//   requires v.WF(k)
// {
//   forall i:nat | k.ValidIdx(i) && Between(start, i, end) :: v.highest_heard[i] > k.ids[i]
// }
// 
// predicate OnChordHeardDominatesIdInv(k: Constants, v: Variables)
//   requires k.WF()
//   requires v.WF(k)
// {
//   forall start:nat, end:nat | k.ValidIdx(start) && k.ValidIdx(end) && IsChord(k, v, start, end) :: OnChordHeardDominatesId(k, v, start, end)
// }

predicate Between(k: Constants, startExclusive: nat, i: nat, endExclusive: nat)
{
  if startExclusive < endExclusive
  then
    startExclusive < i < endExclusive
  else
    startExclusive < i || i < endExclusive
}

predicate IsChord(k: Constants, v: Variables, start: nat, end: nat)
{
  && k.WF()
  && v.WF(k)
  && k.ValidIdx(start)
  && k.ValidIdx(end)
  && k.ids[start] == v.highest_heard[end]
}
predicate HeardOnChordDominatesID(k: Constants, v: Variables, start: nat, end: nat)
  requires k.WF()
  requires v.WF(k)
{
  forall i:nat | k.ValidIdx(i) && Between(k, start, i, end) :: v.highest_heard[i] > k.ids[i]
}

predicate HeardDominatesInv(k: Constants, v: Variables)
{
  && (forall start, end | k.ValidIdx(start) && k.ValidIdx(end) && IsChord(k, v, start, end) :: HeardOnChordDominatesID(k, v, start, end))
}


predicate Inv(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
//  && OnChordHeardDominatesIdInv(k, v)
  && HeardDominatesInv(k, v)
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
  assert exists step :: NextStep(k, v, v', step);
  var step :| NextStep(k, v, v', step);
  var src := step.src;
  var dst := NextIdx(k, src);
  assert Transmission(k, v, v', src);
  forall start:nat, end:nat | k.ValidIdx(start) && k.ValidIdx(end) && IsChord(k, v', start, end) ensures HeardOnChordDominatesID(k, v', start, end)
  {
    var message := max(v.highest_heard[src], k.ids[src]);
    var dst_new_max := max(v.highest_heard[dst], message);

    if IsChord(k, v', start, end) {
      forall i:nat | k.ValidIdx(i) && Between(k, start, i, end)
        ensures v'.highest_heard[i] > k.ids[i]
      {
        if dst==end {
          // which of the three values did highest_heard[dst] take on?
          if v'.highest_heard[dst] == v.highest_heard[dst] {
            assert v'.highest_heard[i] > k.ids[i];
          } else if v'.highest_heard[dst] == k.ids[src] {
            calc {
              k.ids[src];
                // this branch
              == v'.highest_heard[dst];
                // IsChord
              == k.ids[start];
            }
            assert src!=start;
            assert k.UniqueIds(); // WTF
            assert v'.highest_heard[i] > k.ids[i];
          } else {
//            if i==src {
//              assert v.highest_heard[i] > k.ids[i];
//              assert v'.highest_heard[i] > k.ids[i];
//            } else {
//              assert Between(k, start, i, src);
//              assert v'.highest_heard[i] > k.ids[i];
//            }
            assert v'.highest_heard[i] > k.ids[i];
          }
        } else if dst==start {
          assert v'.highest_heard[i] > k.ids[i];
        } else if Between(k, start, dst, end) {
          assert v'.highest_heard[i] > k.ids[i];
        } else if Between(k, end, dst, start) {
          assert v'.highest_heard[i] > k.ids[i];
        } else {
          assert false;
        }
      }
      assert HeardOnChordDominatesID(k, v', start, end);
    }
  }
}

lemma InvImpliesSafety(k: Constants, v: Variables)
  requires Inv(k, v)
  ensures Safety(k, v)
{
}
