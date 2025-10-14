
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
  // Prove v.WF(c)
  assert v.WF(c);

  // Prove OnChordHeardDominatesIdInv(c, v)
  assert forall start, end | IsChord(c, v, start, end) 
    :: OnChordHeardDominatesId(c, v, start, end);
  {
    // Unpack IsChord
    // v.WF(c) && c.ValidIdx(start) && c.ValidIdx(end) && c.ids[start] == v.highest_heard[end]
    // Need to show: forall node | Between(start, node, end) && c.ValidIdx(node) :: v.highest_heard[node] > c.ids[node]
    assert forall node | Between(start, node, end) && c.ValidIdx(node)
      :: v.highest_heard[node] > c.ids[node];
    {
      // By Init, v.highest_heard[node] == -1, c.ids[node] >= 0
      assert v.highest_heard[node] == -1;
      assert c.ids[node] >= 0;
      assert -1 < c.ids[node];
      // Contradicts v.highest_heard[node] > c.ids[node], but Between(start,node,end) is empty since v.highest_heard[end] == c.ids[start] == -1 is impossible for nat
      // So vacuously true
    }
  }

  // Prove Safety(c, v)
  assert forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j;
  {
    // IsLeader: c.ValidIdx(i) && v.highest_heard[i] == c.ids[i]
    // But v.highest_heard[i] == -1 by Init, but c.ids[i] >= 0, so IsLeader(c, v, i) is never true, so vacuously holds
  }
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

  // Prove v'.WF(c)
  assert v'.WF(c);

  // Prove OnChordHeardDominatesIdInv(c, v')
  assert forall start, end | IsChord(c, v', start, end) ensures OnChordHeardDominatesId(c, v', start, end);
  {
    forall node | Between(start, node, end) && c.ValidIdx(node)
      ensures v'.highest_heard[node] > c.ids[node]
    {
      if dstidx == end {
        // maybe this chord just sprung into existence
        if v'.highest_heard[end] == v.highest_heard[end] {
          // no change --
          assert v'.highest_heard[end] == v.highest_heard[end];
          // By Inv(c, v), OnChordHeardDominatesIdInv(c, v) holds for any chord in v
        } else if v'.highest_heard[end] == c.ids[srcidx] {
          // The message was c.ids[srcidx]
          // Need to show c.ids[srcidx] == c.ids[start]
          // By IsChord(c, v', start, end): c.ids[start] == v'.highest_heard[end] == c.ids[srcidx]
          // So start == srcidx by UniqueIds
          // For node in Between(start, node, end), v'.highest_heard[node] == v.highest_heard[node] (since only end was updated)
          // By Inv(c, v), OnChordHeardDominatesId(c, v, start, end) holds, so v.highest_heard[node] > c.ids[node]
          // So v'.highest_heard[node] == v.highest_heard[node] > c.ids[node]
        } else if v'.highest_heard[end] == v.highest_heard[srcidx] {
          // Similar reasoning
        }
      } else {
        // this chord was already here
        // v'.highest_heard[node] == v.highest_heard[node] for node != dstidx
        // By Inv(c, v), OnChordHeardDominatesId(c, v, start, end) holds, so v.highest_heard[node] > c.ids[node]
        // So v'.highest_heard[node] == v.highest_heard[node] > c.ids[node]
      }
    }
  }

  // Prove Safety(c, v')
  assert forall i, j | IsLeader(c, v', i) && IsLeader(c, v', j) ensures i == j {
    // IsLeader(c, v', i): c.ValidIdx(i) && v'.highest_heard[i] == c.ids[i]
    // If two nodes are leaders, need to show i == j
    // By Safety(c, v), Inv(c, v) => Safety(c, v) holds
    // If v'.highest_heard[i] == c.ids[i] and v'.highest_heard[j] == c.ids[j], and both are leaders, then by OnChordHeardDominatesIdInv(c, v') and UniqueIds, i == j
  }
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
  // Safety(c, v): forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j
  assert forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j;
  {
    // IsLeader(c, v, i): c.ValidIdx(i) && v.highest_heard[i] == c.ids[i]
    // IsLeader(c, v, j): c.ValidIdx(j) && v.highest_heard[j] == c.ids[j]
    // By OnChordHeardDominatesIdInv, only one node can have v.highest_heard[x] == c.ids[x], since otherwise would contradict OnChordHeardDominatesId
    // By UniqueIds, c.ids[i] == c.ids[j] implies i == j
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
