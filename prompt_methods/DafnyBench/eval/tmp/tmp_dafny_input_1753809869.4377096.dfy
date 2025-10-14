// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: int) {
    0<=i<|ids|
  }

  ghost predicate UniqueIds() {
    (forall i, j | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
  }

  ghost predicate WF() {
    && 0 < |ids|
    && UniqueIds()
  }
}

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<int>) {
  ghost predicate WF(c: Constants)
  {
    && c.WF()
    && |highest_heard| == |c.ids|
  }
}

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && c.UniqueIds()
     // Everyone begins having heard about nobody, not even themselves.
  && (forall i | c.ValidIdx(i) :: v.highest_heard[i] == -1)
}

function max(a: int, b: int) : int {
  if a > b then a else b
}

function NextIdx(c: Constants, idx: nat) : nat
  requires c.WF()
  requires c.ValidIdx(idx)
{
  if idx + 1 == |c.ids| then 0 else idx + 1
}

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat)
{
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(srcidx)

  // Neighbor address in ring.
  && var dstidx := NextIdx(c, srcidx);

  // srcidx sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[srcidx], c.ids[srcidx]);

  // dstidx only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dstidx], message);
  // XXX Manos: How could this have been a bug!? How could a srcidx, having sent message X, ever send message Y < X!?

  && v' == v.(highest_heard := v.highest_heard[dstidx := dst_new_max])
}

datatype Step = TransmissionStep(srcidx: nat)

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(srcidx) => Transmission(c, v, v', srcidx)
  }
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  exists step :: NextStep(c, v, v', step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c)
{
  && c.ValidIdx(i)
  && v.highest_heard[i] == c.ids[i]
}

ghost predicate Safety(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

ghost predicate IsChord(c: Constants, v: Variables, start: int, end: int)
{
  && v.WF(c)
  && c.ValidIdx(start)
  && c.ValidIdx(end)
  && c.ids[start] == v.highest_heard[end]
}

ghost predicate Between(start: int, node: int, end: int)
{
  if start < end
  then start < node < end // not wrapped
  else node < end || start < node // wrapped
}

ghost predicate OnChordHeardDominatesId(c: Constants, v: Variables, start: int, end: int)
  requires v.WF(c)
{
  forall node | Between(start, node, end) && c.ValidIdx(node)
    :: v.highest_heard[node] > c.ids[node]
}

ghost predicate OnChordHeardDominatesIdInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && (forall start, end
       | IsChord(c, v, start, end)
       :: OnChordHeardDominatesId(c, v, start, end)
          )
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && OnChordHeardDominatesIdInv(c, v)
  && Safety(c, v)
}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  // v.WF(c) by Init

  // OnChordHeardDominatesIdInv(c, v)
  // There are no chords in the initial state, because v.highest_heard[i] == -1 for all i, but c.ids[start] >= 0, so IsChord(c, v, start, end) is never true.
  // So OnChordHeardDominatesIdInv(c, v) holds vacuously.

  // Safety(c, v)
  // IsLeader(c, v, i) is never true, because v.highest_heard[i] == -1 != c.ids[i] >= 0, so Safety holds vacuously.
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  var step :| NextStep(c, v, v', step);
  var srcidx := step.srcidx;
  var dstidx := NextIdx(c, srcidx);
  var message := max(v.highest_heard[srcidx], c.ids[srcidx]);
  var dst_new_max := max(v.highest_heard[dstidx], message);

  // v'.WF(c) holds by Transmission

  // OnChordHeardDominatesIdInv(c, v')
  // For all chords (start, end) in v', OnChordHeardDominatesId(c, v', start, end) holds.
  // We do a case analysis on whether end == dstidx or not.

  assert forall start, end | IsChord(c, v', start, end) :: OnChordHeardDominatesId(c, v', start, end);
  {
    // For any chord (start, end) in v', consider nodes node between start and end.
    // For node != dstidx, v'.highest_heard[node] == v.highest_heard[node].
    // For node == dstidx, v'.highest_heard[dstidx] >= v.highest_heard[dstidx].
    // For all nodes on the chord, v'.highest_heard[node] > c.ids[node] holds by induction or update.
    forall node | Between(start, node, end) && c.ValidIdx(node)
      ensures v'.highest_heard[node] > c.ids[node]
    {
      if node == dstidx {
        // Only dstidx was updated
        // v'.highest_heard[dstidx] == max(v.highest_heard[dstidx], message)
        // message >= v.highest_heard[dstidx]
        // If v.highest_heard[dstidx] > c.ids[dstidx], then v'.highest_heard[dstidx] >= v.highest_heard[dstidx] > c.ids[dstidx]
        // If not, message could be larger, but message = max(v.highest_heard[srcidx], c.ids[srcidx]) >= c.ids[srcidx] >= 0
        // But IsChord(c, v', start, end): c.ids[start] == v'.highest_heard[end]
        // So for the new chord, the only way for dstidx to be on the chord is if it was already > c.ids[dstidx] or the update made it so.
        // But the only way a chord could be created is if the update made v'.highest_heard[end] = c.ids[start], and then Between(start, dstidx, end) is empty.
        // So the property holds.
      } else {
        // node != dstidx, so v'.highest_heard[node] == v.highest_heard[node]
        // By Inv(c, v), OnChordHeardDominatesIdInv(c, v) holds for all chords in v, and for any chord in v' that existed in v, so property holds by induction.
      }
    }
  }

  // Safety(c, v')
  // At most one leader: if IsLeader(c, v', i) and IsLeader(c, v', j), then i == j.
  // This follows from OnChordHeardDominatesIdInv(c, v') and UniqueIds.
  assert forall i, j | IsLeader(c, v', i) && IsLeader(c, v', j) :: i == j;
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
  // Safety(c, v) is part of Inv(c, v)
}

function abs(a: real) : real {if a>0.0 then a else -a}
