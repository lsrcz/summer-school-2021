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
datatype Variables = Variables(highest_heard: seq<int>) {
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

function max(a: int, b: int) : int {
  if a > b then a else b
}

function NextIdx(k: Constants, idx: nat) : nat
  requires k.WF()
  requires k.ValidIdx(idx)
{
//  (idx + 1) % |k.ids|
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
{
  IsChord(k, v, start, end)
  ==> (forall i:nat | k.ValidIdx(i) && Between(k, start, i, end) :: v.highest_heard[i] > k.ids[i])
}

predicate HeardDominatesInv(k: Constants, v: Variables)
{
  && (forall start, end | k.ValidIdx(start) && k.ValidIdx(end) :: HeardOnChordDominatesID(k, v, start, end))
}

predicate Inv(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
  && Safety(k, v)
  && HeardDominatesInv(k, v)
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
  var step :| NextStep(k, v, v', step);
  assert Transmission(k, v, v', step.src);
  forall start:nat, end:nat | k.ValidIdx(start) && k.ValidIdx(end) ensures HeardOnChordDominatesID(k, v', start, end)
  {
    if (
      && k.WF()
      && v'.WF(k)
      && k.ValidIdx(start)
      && k.ValidIdx(end)
      && k.ids[start] == v'.highest_heard[end]
    ) {
      forall i:nat | k.ValidIdx(i) && Between(k, start, i, end)
        ensures v'.highest_heard[i] > k.ids[i]
      {
        // case analysis step 1: dst changed. Was it between start,end,
        // equal to start or end, or on the opposide side (end,start)?
        // answer -> only dst==end matters.
//        if Between(k, start, dst, end) {
//          assert v'.highest_heard[i] > k.ids[i];
//        } else if dst==end {
//          assert v'.highest_heard[i] > k.ids[i];
//        } else if dst==start {
//          assert v'.highest_heard[i] > k.ids[i];
//        } else {
//          assert v'.highest_heard[i] > k.ids[i];
//        }

        var src := step.src;
        var dst := NextIdx(k, src);
        if dst==end {
          // case analysis step 2:
          // did dst take on k.ids[src], v.highest_heard[src], or
          // v.highest_heard[dst]?
          if v'.highest_heard[dst] == v.highest_heard[dst] {
            // nothing changed.
            assert v'.highest_heard[i] > k.ids[i];
          } else if v'.highest_heard[dst] == v.highest_heard[src] {
            // src got extended to dst, which means that start->end
            // must have gone start->src in prior state.
            assert IsChord(k, v, start, src);
            if (i==dst) {
              // src now included in extended chord.
              assert v'.highest_heard[i] > k.ids[i];
            } else if (i==src) {
              assume false;
              assert v'.highest_heard[i] > k.ids[i]; //here
            } else {
              // Covered by prior-state chord.
              assert Between(k, start, i, dst);
              if start < dst {
                assert start < i < dst;
                assert src < dst;
                assert i < src;
                assert Between(k, start, i, src);
              } else {
                assert Between(k, start, i, src);
              }
              assert v'.highest_heard[i] > k.ids[i];
            }
            assert v'.highest_heard[i] > k.ids[i];
          } else {
            // dst got src's id, and that was *higher* than src's highest
            // heard,
            assert v'.highest_heard[dst] == k.ids[src];
            // which means that this chord must have started at src.
            assert k.ids[start] == k.ids[src];
            assert k.UniqueIds();
            assert src == start;
            assert v'.highest_heard[i] > k.ids[i]; // and here
          }
        } else {
          assert v'.highest_heard[i] > k.ids[i];
        }
      }
    }
  }
}

lemma InvImpliesSafety(k: Constants, v: Variables)
  requires Inv(k, v)
  ensures Safety(k, v)
{
}
