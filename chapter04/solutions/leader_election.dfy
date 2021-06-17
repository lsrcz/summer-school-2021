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
  // TODO let's try it with modulo, too.
  && var dst := NextIdx(k, src);
  // Yeah turns out modulo makes dafny stupid.
  // && var dst := (src + 1) % |k.ids|;

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

// TODO note that the elected leader isn't stable, which isn't ideal.
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

function GetIndexWithMaxIdInner(k: Constants, limit: nat) : (idx:nat)
  requires 0 < limit <= |k.ids|
  ensures 0 <= idx < limit
  ensures forall j:nat | 0<=j<limit :: k.ids[j] <= k.ids[idx]
{
  if limit==1
  then 0
  else
    var prevIdx := GetIndexWithMaxIdInner(k, limit-1);
    var thisId := k.ids[limit-1];
    if k.ids[prevIdx] >= thisId
    then prevIdx
    else limit-1
}

function GetIndexWithMaxId(k: Constants) : nat
  requires 0 < |k.ids|
{
  GetIndexWithMaxIdInner(k, |k.ids|)
}

predicate Between(k: Constants, startExclusive: nat, idx: nat, endInclusive: nat)
  requires ValidIdx(k, startExclusive)
  requires ValidIdx(k, idx)
  requires ValidIdx(k, endInclusive)
{
  if startExclusive < endInclusive
  then startExclusive < idx <= endInclusive
  else idx <= endInclusive || startExclusive < idx
}

// An identifier that has "reached" a distant node some way around the
// ring is at least as high as the highest_heard of every index it has
// passed.
predicate IDOnChordDominatesHeard(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i:nat, j:nat | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i] == s.highest_heard[j] ::
    forall m:nat | ValidIdx(k, m) && Between(k, i, m, j) :: s.highest_heard[m] >= k.ids[i]
}

// An identifier that has "reached" a distant node some way around the
// ring is at least as high as the id of every node it has passed.
predicate IDOnChordDominatesIDs(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i:nat, j:nat | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i] == s.highest_heard[j] && i != j::
    forall m:nat | ValidIdx(k, m) && Between(k, i, m, j) :: k.ids[i] >= k.ids[m]
}

predicate HighestHeardDominatesID(k: Constants, s: Variables)
  requires WF(k, s)
{
  forall i:nat | ValidIdx(k, i) && s.highest_heard[i] != -1 :: s.highest_heard[i] >= k.ids[i]
}

predicate Inv(k: Constants, s: Variables)
{
  && WF(k, s)
  && Safety(k, s)
  && InvPred(k, s)
  && IDOnChordDominatesHeard(k, s)
  && IDOnChordDominatesIDs(k, s)
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
  //assume Inv(k, s);
  var step :| NextStep(k, s, s', step);
  assert (forall i:nat | ValidIdx(k, i) && !IsMaxId(k, k.ids[i]) :: !IsLeader(k, s, i));
  assert Transmission(k, s, s', step.src);
  /*forall i:nat, j:nat | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i] == s'.highest_heard[j] ensures
    forall m:nat | ValidIdx(k, m) && Between(k, i, m, j) :: s'.highest_heard[m] >= k.ids[i] {
    forall m:nat | ValidIdx(k, m) && Between(k, i, m, j) ensures s'.highest_heard[m] >= k.ids[i] {
      var src := step.src;
      var dest := NextIdx(k, src);
      if |k.ids|==1 {
        assert s'.highest_heard[m] >= k.ids[i];
      } else if dest == j {
        assert src != dest;
        if m == j {
          assert s'.highest_heard[m] >= k.ids[i];
        } else {
          if s'.highest_heard[j] == k.ids[src] {
            // new little chord -- should be a contradiction
            assert s.highest_heard[src] == s'.highest_heard[src];
            assert s.highest_heard[m] == s'.highest_heard[m];
            assert forall ii:nat, ij:nat | ValidIdx(k, ii) && ValidIdx(k, ij) && k.ids[ii] == s.highest_heard[ij] ::
                forall im:nat | ValidIdx(k, im) && Between(k, ii, im, ij) :: k.ids[ii] > k.ids[im];

            if (s.highest_heard[j] != k.ids[src]) {
                if(k.ids[src] > k.ids[i]) {
                    assert s'.highest_heard[m] >= k.ids[i];
                } else if (k.ids[src] < k.ids[i]) {
                    assert s'.highest_heard[m] >= k.ids[i];
                } else {
                    assert k.ids[src] == k.ids[i];
                    assert src == i;
                    assert s'.highest_heard[m] >= k.ids[i];
                }
            } else {
                //assert s.highest_heard[m] >= k.ids[i];
                //assert s'.highest_heard[m] >= k.ids[i];
                assert false;
            }
          } else {
            assert s'.highest_heard[m] >= k.ids[i];
          }
        }
      } else {
        // should be easy by virtue of invariants on s being the same
        assert s'.highest_heard[m] >= k.ids[i];
      }
    }
  }*/

  /*forall i:nat | ValidIdx(k, i) && s'.highest_heard[i] != -1 ensures s'.highest_heard[i] >= k.ids[i] {
    var src := step.src;
    var dest := NextIdx(k, src); 
    if (dest == i) {
      assert s'.highest_heard[i] == 
      assert s'.highest_heard[i] >= k.ids[i];
    } else {
      assert s'.highest_heard[i] >= k.ids[i];
    } 
  }*/
  assert HighestHeardDominatesID(k, s');
  assert IDOnChordDominatesHeard(k, s');
  /*forall i:nat, j:nat | ValidIdx(k, i) && ValidIdx(k, j) && k.ids[i] == s'.highest_heard[j] && i != j ensures
    forall m:nat | ValidIdx(k, m) && Between(k, i, m, j) :: k.ids[i] >= k.ids[m] {
    forall m:nat | ValidIdx(k, m) && Between(k, i, m, j) ensures k.ids[i] >= k.ids[m] {
      var src := step.src;
      var dest := NextIdx(k, src);
      if |k.ids|==1 {
      } else {
        if(m == i) {      
          assert k.ids[i] >= k.ids[m];
        } else if (m == j) {
          if(dest == j) {
            if s'.highest_heard[dest] == k.ids[src] {
              assert k.ids[i] >= k.ids[m];
            } else {
              assert k.ids[i] >= k.ids[m];
            }
          } else {
            assert k.ids[i] >= k.ids[m];
          }
        } else {
          assert k.ids[i] >= k.ids[m];
        }
      }            
    }
  }*/
  assert IDOnChordDominatesIDs(k, s');
  forall i:nat | ValidIdx(k, i) && !IsMaxId(k, k.ids[i]) ensures !IsLeader(k, s', i) {
    var src := step.src;
    var dest := NextIdx(k, src);
    if |k.ids|==1 {
      forall j:nat | ValidIdx(k, j) ensures k.ids[j] <= i {
        assert j == i;
      }
      assert IsMaxId(k,k.ids[i]);
      //assert !IsLeader(k, s', i);
    } else if i == src {
      assert !IsLeader(k, s, i);
      assert !IsLeader(k, s', i);
    } else if i == dest {
      assert !IsLeader(k, s, i);
      assert !IsLeader(k, s', i);
    } else {
      assert !IsLeader(k, s', i);
    }
  }
  assert InvPred(k, s');
//  forall i, j | IsLeader(k, s', i) && IsLeader(k, s', j)
//  ensures i == j
//  {
//    //here
//  }
//  forall i | ValidIdx(k, i) && !IsMaxId(k, i)
//  ensures !IsLeader(k, s', i)
//  {
//    //here
//  }::
//  assert Safety(k, s');
//  assert InvPred(k, s');
}

lemma InvImpliesSafety(k: Constants, s: Variables)
  requires Inv(k, s)
  ensures Safety(k, s)
{
}
