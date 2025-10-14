
// We'll define "Between" to capture how the ring wraps around.
// SOLUTION
ghost predicate Between(start: nat, i: nat, end: nat)
{
  if start < end then start < i < end
  else i < end || start < i
}

lemma BetweenTests()
{
  // when start >= end, behavior is a bit tricker
  // before end
  assert Between(3, 1, 2) == (1 < 2 || 3 < 1); // true
  // after start
  assert Between(3, 4, 2) == (4 < 2 || 3 < 4); // true
  // not in this range
  assert !Between(3, 2, 2); // false
}
// END

// ids gives each node's (unique) identifier (address)
//
// highest_heard[i] is the highest other identifier the node at index i has
// heard about (or -1 if it has heard about nobody - note that -1 is not a valid identifier).
datatype Variables = Variables(ids: seq<nat>, highest_heard: seq<int>) {

  ghost predicate ValidIdx(i: int) {
    0<=i<|ids|
  }

  ghost predicate UniqueIds() {
    forall i, j | ValidIdx(i) && ValidIdx(j) ::
      ids[i]==ids[j] ==> i == j
  }

  ghost predicate WF()
  {
    && 0 < |ids|
    && |ids| == |highest_heard|
  }

  // We'll define an important predicate for the inductive invariant.
  // SOLUTION
  // `end` thinks `start` is the highest
  ghost predicate IsChord(start: nat, end: nat)
  {
    && ValidIdx(start) && ValidIdx(end)
    && WF()
    && highest_heard[end] == ids[start]
  }
  // END
}

ghost predicate Init(v: Variables)
{
  && v.UniqueIds()
  && v.WF()
     // Everyone begins having heard about nobody, not even themselves.
  && (forall i | v.ValidIdx(i) :: v.highest_heard[i] == -1)
}

ghost function max(a: int, b: int) : int {
  if a > b then a else b
}

ghost function NextIdx(v: Variables, idx: nat) : nat
  requires v.WF()
  requires v.ValidIdx(idx)
{
  // for demo we started with a definition using modulo (%), but this non-linear
  // arithmetic is less friendly to Dafny's automation
  // SOLUTION
  if idx == |v.ids| - 1 then 0 else idx + 1
  // END
}

// The destination of a transmission is determined by the ring topology
datatype Step = TransmissionStep(src: nat)

// This is an atomic step where src tells its neighbor (dst, computed here) the
// highest src has seen _and_ dst updates its local state to reflect receiving
// this message.
ghost predicate Transmission(v: Variables, v': Variables, step: Step)
  requires step.TransmissionStep?
{
  var src := step.src;
  && v.WF()
  && v.ValidIdx(src)
  && v'.ids == v.ids

  // Neighbor address in ring.
  && var dst := NextIdx(v, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], v.ids[src]);

  // dst only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dst], message);

  // demo has a bug here
  // SOLUTION
  && v'.highest_heard == v.highest_heard[dst := dst_new_max]
  // END
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(_) => Transmission(v, v', step)
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsLeader(v: Variables, i: int)
  requires v.WF()
{
  && v.ValidIdx(i)
  && v.highest_heard[i] == v.ids[i]
}

ghost predicate Safety(v: Variables)
  requires v.WF()
{
  forall i, j | IsLeader(v, i) && IsLeader(v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

// SOLUTION
ghost predicate ChordHeardDominated(v: Variables, start: nat, end: nat)
  requires v.IsChord(start, end)
  requires v.WF()
{
  forall i | v.ValidIdx(i) && Between(start, i, end) ::
    v.highest_heard[i] > v.ids[i]
}

// We make this opaque so Dafny does not use it automatically; instead we'll use
// the lemma UseChordDominated when needed. In many proofs opaqueness is a way
// to improve performance, since it prevents the automation from doing too much
// work; in this proof it's only so we can make clear in the proof when this
// invariant is being used.
ghost predicate {:opaque} OnChordHeardDominatesId(v: Variables)
  requires v.WF()
{
  forall start: nat, end: nat | v.IsChord(start, end) ::
    ChordHeardDominated(v, start, end)
}

lemma UseChordDominated(v: Variables, start: nat, end: nat)
  requires v.WF()
  requires OnChordHeardDominatesId(v)
  requires v.IsChord(start, end )
  ensures ChordHeardDominated(v, start, end)
{
  reveal OnChordHeardDominatesId();
}
// END


ghost predicate Inv(v: Variables)
{
  && v.WF()
     // The solution will need more conjuncts
     // SOLUTION
  && v.UniqueIds()
  && OnChordHeardDominatesId(v)
     // Safety is not needed - we can prove it holds from the other invariants
     // END
}

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{
  // SOLUTION
  // UniqueIds and WF are immediate from Init
  // Now, show OnChordHeardDominatesId holds vacuously (no chords)
  reveal OnChordHeardDominatesId();
  // For any start, end: v.IsChord(start, end) is false in the initial state
  forall start: nat, end: nat | v.IsChord(start, end)
    ensures ChordHeardDominated(v, start, end)
  {
    // v.IsChord(start, end) requires v.highest_heard[end] == v.ids[start]
    // But v.highest_heard[end] == -1 in Init, and v.ids[start] >= 0
    assert v.highest_heard[end] == -1;
    assert v.ids[start] >= 0;
    assert v.highest_heard[end] != v.ids[start];
    // So this branch is unreachable
  }
  // END
}

lemma NextPreservesInv(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  // SOLUTION
  // UniqueIds and WF are preserved
  // Now, show OnChordHeardDominatesId(v') holds
  reveal OnChordHeardDominatesId();
  // For any start, end, if v'.IsChord(start, end), show ChordHeardDominated(v', start, end)
  forall start: nat, end: nat | v'.IsChord(start, end)
    ensures ChordHeardDominated(v', start, end)
  {
    // There are three cases:
    // (1) The chord at (start, end) existed in v, and dst != end: unchanged
    // (2) The chord at (start, end) is new, i.e. dst == end and v'.highest_heard[end] == v.ids[start]
    // (3) The chord at (start, end) is extended from a previous chord (start, src), i.e. dst == end and v'.highest_heard[end] == v.highest_heard[src]
    var src := step.src;
    var dst := NextIdx(v, src);
    var message := max(v.highest_heard[src], v.ids[src]);
    var dst_new_max := max(v.highest_heard[dst], message);

    if dst != end {
      // The update does not affect end, so chord is unchanged
      if v.IsChord(start, end) {
        UseChordDominated(v, start, end);
      } else {
        // The chord is new, but dst != end, so highest_heard[end] unchanged from v, so can't be a chord unless it was already one
        // So ChordHeardDominated holds vacuously
      }
    } else {
      // dst == end, so highest_heard[end] may have changed
      if v'.highest_heard[end] == v.ids[start] {
        // New chord: highest_heard[end] == ids[start]
        // For all i between start and end, highest_heard[i] > ids[i]
        // But for all i != end, highest_heard[i] unchanged, and for end, highest_heard[end] == ids[start] >= 0 > ids[end] (since ids are unique and >= 0)
        // So ChordHeardDominated holds vacuously (no i with Between(start, i, end))
      } else if v'.highest_heard[end] == v.highest_heard[src] {
        // Chord is extended from (start, src)
        if v.IsChord(start, src) {
          UseChordDominated(v, start, src);
        }
      } else {
        // The update did not create a new chord, so if chord existed before, use previous
        if v.IsChord(start, end) {
          UseChordDominated(v, start, end);
        }
      }
    }
  }
  // END
}

lemma InvImpliesSafety(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{
  // SOLUTION
  // If two nodes are leaders, they must be the same node
  forall i: nat, j: nat | IsLeader(v, i) && IsLeader(v, j)
    ensures i == j
  {
    if i != j {
      // Both i and j are leaders, so highest_heard[i] == ids[i], highest_heard[j] == ids[j]
      // But by ChordHeardDominated, for chord (i, i), all nodes between i and i have highest_heard[k] > ids[k]
      UseChordDominated(v, i, i);
      // Contradicts highest_heard[i] == ids[i]
      assert v.highest_heard[i] == v.ids[i];
      assert !(v.highest_heard[i] > v.ids[i]);
      // Contradiction
      assert false;
    }
  }
  // END
}

function abs(a: real) : real {if a>0.0 then a else -a}
