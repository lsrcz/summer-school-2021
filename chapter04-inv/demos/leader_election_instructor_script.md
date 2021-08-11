 // case analysis step 1: dst changed. Was it between start,end,
        // equal to start or end, or on the opposide side (end,start)?
        // answer -> only dst==end matters.


          // case analysis step 2:
          // did dst take on k.ids[src], v.highest_heard[src], or
          // v.highest_heard[dst]?
              // src now included in extended chord.
              // Covered by prior-state chord.
            ...becmose a Between argument that reveals UniqueIDs problem.

            // dst got src's id, and that was *higher* than src's highest
            // heard,
            // which means that this chord must have started at src.
            

Okay, so my fellow verification engineer banged out this lovely specification for
leader election.
Let's read it.

Alex the Engineer had to go on vacation before completing the proof work, so Alex left me
with this file. Let's get it verifying!
We'll study the spec carefully.
Then we'll begin by assuming the protocol is correct and try to figure out why
stupid old Dafny doesn't understand Alex's brilliance.

docker container run -t -i --mount src="`pwd`",target=/home/dafnyserver/work,type=bind --workdir /home/dafnyserver/work jonhdotnet/summer_school:1.1 /bin/bash

- fix the type inference failures on nat
- in my test run, it got really slow. Add /timeLimit:20
- break out the profiler:
  ```../../tools/dafny-profile.py 20 "*NextPreservesInv" leader_election_work.dfy```
  - huh, no frequent quantifier instantiations

(voodoo) So we try noNLarith to see if Z3 is getting hung up on nonlinear algebraic reductions.
Yep, now it fails quickly.
Where do we have nonlinear arithmetic? Ugh, that mod. We don't really need mod here,
so instead of teaching you how to manage mod, let's just bail on it.

(BUG #1 was "idx + 0", but I'm not going to re-introduce that one.)

So time to dig into the broken proof.
* Choose a step. (get through the exists, skolemize the step choice & params)

...wait, why would this even work? Safety is like the manhole: a good property, but not
inductive. Lots of system states that are a step away from Safety but shouldn't be
reachable.
It's time to ask *why* should the system work? What's the key intuition?
The answer is in the animation: As "big" identifiers work around the ring, they
build "chords" from their origin to the farthest point they've reached.
Sometimes one chord will gobble up another's head, breaking it, but anytime there is a
chord, all the nodes it has passed over have heard about it and are dominated by it.
The biggest ID's chord never gets gobbled; eventually it reaches all the way around the ring.

Type out IsChord, OnChordHeardDominatesId.

Cheat sheet:
```
  predicate Between(start: nat, i: nat, end: nat)
  {
    if start<end
    then start<i<end
    else i<end || start<i
  }

  predicate IsChord(k: Constants, v: Variables, start: nat, end: nat)
  {
    && k.WF()
    && v.WF(k)
    && k.ValidIdx(start)
    && k.ValidIdx(end)
    && k.ids[start] == v.highest_heard[end]
  }

  predicate OnChordHeardDominatesId(k: Constants, v: Variables, start: nat, end: nat)
    requires k.WF()
    requires v.WF(k)
  {
    forall i:nat | k.ValidIdx(i) && Between(start, i, end) :: v.highest_heard[i] > k.ids[i]
  }

  predicate OnChordHeardDominatesIdInv(k: Constants, v: Variables)
    requires k.WF()
    requires v.WF(k)
  {
    forall start:nat, end:nat | k.ValidIdx(start) && k.ValidIdx(end) && IsChord(k, v, start, end) :: OnChordHeardDominatesId(k, v, start, end)
  }
```

Proof sketch:
If we are gonna violate Safety, we'll need two idxes i, j tha
leader. WOLOG let i be the one with the larger id. It is leader, so IsChord(k,v,i,i).
So every *other* node, including j is Between(k, i, j, i), so
v.highest_heard[j] > k.ids[j], which is a contradiction with IsLeader(j).

...need to define Between.
Could require k.ValidIdx on all args, but meh, don't need to.
Note that start and end are exclusive:
* Since the start doesn't adjust its own highest_heard based on its own id, it's not
  affected by the message traveling along the chord.
* Since end can be equal to start when the chord completes the ring, we don't want to
  include it, since it *won't* have highest_heard > id.
** name inductive predicate, use ValidIdx

Try to nail down Safety first.
  -- try the contradiction above; punchline is a trigger OnChordHeardDominatesId

Use a case analysis on dst
  - discrete cases first, then Betweens -- dafny seems to do better.
    { dst==end, dst==start, Between(start,dst,end), Between(end,dst,start), false }
  - in dst==end case, split on which thing was max,
      { v'.highest_heard[dst] == v.highest_heard[dst],
        v'.highest_heard[dst] == k.ids[src],
        v'.highest_heard[dst] == v.highest_heard[src] }
    # FIX discover (in else branch) that we screwed up the assignment, ignoring dst_new_max
    # in middle branch (k.ids[src]), assert:
      k.ids[src] == v'.highest_heard[dst] // this branch
      v'.highest_heard[dst] == k.ids[start] // IsChord
      assert src!=start // no idea why XXX-TODO
      assert k.UniqueIds() // WTF -- FIX by adding to Constants.WF
...now the proof goes through.


*** TODO -- XXX
Image fixes:
For "assume" get the calvin & hobbes strip
***


------------------------------------------------------------------------------

# Another run-through.

Fresh file. Run Dafny.
* "value does not satisfy the subset constraints..."
* fix those three, then a timeout!?
```
../../tools/dafny-profile.py 20 "*NextPreservesInv" leader_election_work.dfy 
```
No quantifiers instantiated more than 1000 times.

* try noNLarith
dafny leader_election_work.dfy /noNLarith
Fails fast

nlarith lecture

```
  if idx+1 == |k.ids| then 0 else idx+1
```

XXX does the inductive invariant lesson preced this one?

# Define invariant

...wait, why would this even work? Safety is like the manhole: a good property, but not
inductive. Lots of system states that are a step away from Safety but shouldn't be
reachable.
It's time to ask *why* should the system work? What's the key intuition?
The answer is in the animation: As "big" identifiers work around the ring, they
build "chords" from their origin to the farthest point they've reached.
Sometimes one chord will gobble up another's head, breaking it, but anytime there is a
chord, all the nodes it has passed over have heard about it and are dominated by it.
The biggest ID's chord never gets gobbled; eventually it reaches all the way around the ring.

FIX Type out IsChord, OnChordHeardDominatesId.

Cheat sheet:
```
  predicate Between(start: nat, i: nat, end: nat)
  {
    if start<end
    then start<i<end
    else i<end || start<i
  }

  predicate IsChord(k: Constants, v: Variables, start: nat, end: nat)
  {
    && k.WF()
    && v.WF(k)
    && k.ValidIdx(start)
    && k.ValidIdx(end)
    && k.ids[start] == v.highest_heard[end]
  }

  predicate OnChordHeardDominatesId(k: Constants, v: Variables, start: nat, end: nat)
    requires k.WF()
    requires v.WF(k)
  {
    forall i:nat | k.ValidIdx(i) && Between(start, i, end) :: v.highest_heard[i] > k.ids[i]
  }

  predicate OnChordHeardDominatesIdInv(k: Constants, v: Variables)
    requires k.WF()
    requires v.WF(k)
  {
    forall start:nat, end:nat | k.ValidIdx(start) && k.ValidIdx(end) && IsChord(k, v, start, end) :: OnChordHeardDominatesId(k, v, start, end)
  }
```

Proof sketch:
If we are gonna violate Safety, we'll need two idxes i, j that are both the
leader. WOLOG let i be the one with the larger id. It is leader, so IsChord(k,v,i,i).
So every *other* node, including j is Between(k, i, j, i), so
v.highest_heard[j] > k.ids[j], which is a contradiction with IsLeader(j).

...need to define Between.
  - why exclusive?
  - not start, because the NEXT node learn's about start's id. else start would instantly be leader.
  - not end, because end's highest_heard hasn't considered end's id.

* bring assert into NextPreservesInv

* introduce variables.
  :| for step,
  forall-statement for {start,end}, i

* split on dst==end, ...

* split dst==end on 
        if v'.highest_heard[dst] == v.highest_heard[dst] {
        } else if v'.highest_heard[dst] == k.ids[src] {
        } else {
          assert v'.highest_heard[dst] == v.highest_heard[src];
        }
        ...fails middle branch

* middle branch:
          assert k.ids[src] > v.highest_heard[dst];

  WHAT? Assert some true stuff
          assert v'.highest_heard[dst] == dst_new_max;
          assert dst_new_max != v.highest_heard[src];
          assert dst_new_max == message;
          assert message > v.highest_heard[dst];
   ...dst_new_max fails!?
          
  look at defn.
  FIX dst_new_max

* okay, still on dst==end and v'.highest_heard[dst] == k.ids[src]
  In this case, we have a little chord from src->dst, but also a chord
  from start->dst.
  So k.ids[src] == k.ids[start];
  That's fine if src==start, but that would exclude
  Between(start, i, dst).
  So src!=start.
  assert k.UniqueIds()!
  FIX UniqueIds.


