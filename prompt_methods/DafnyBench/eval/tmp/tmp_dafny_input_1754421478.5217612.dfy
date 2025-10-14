
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
  // WF
  assert v.WF(c);
  // OnChordHeardDominatesIdInv: vacuously true, since IsChord(c, v, start, end) is false for all start, end
  assert forall start, end | IsChord(c, v, start, end) :: OnChordHeardDominatesId(c, v, start, end);
  // Safety: no leader exists, so vacuously true
  assert forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j;
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

  // 1. v'.WF(c)
  assert v'.WF(c);

  // 2. OnChordHeardDominatesIdInv(c, v')
  forall start, end | IsChord(c, v', start, end)
    ensures OnChordHeardDominatesId(c, v', start, end)
  {
    // For all node between start and end
    forall node | Between(start, node, end) && c.ValidIdx(node)
      ensures v'.highest_heard[node] > c.ids[node]
    {
      // Only v'.highest_heard[dstidx] can differ from v.highest_heard
      if node == dstidx {
        // v'.highest_heard[dstidx] = max(v.highest_heard[dstidx], message)
        // Need to show v'.highest_heard[dstidx] > c.ids[dstidx]
        // Two cases: chord existed before, or chord created by this step
        if v'.highest_heard[dstidx] == v.highest_heard[dstidx] {
          // No change
          assert v.highest_heard[dstidx] > c.ids[dstidx]; // by Inv(c, v)
        } else {
          // v'.highest_heard[dstidx] = message > v.highest_heard[dstidx]
          // message = max(v.highest_heard[srcidx], c.ids[srcidx])
          // We cannot guarantee message > c.ids[dstidx], but
          // IsChord(c, v', start, end) holds, so c.ids[start] == v'.highest_heard[end]
          // node == dstidx == end
          // So c.ids[start] == v'.highest_heard[dstidx]
          // So v'.highest_heard[dstidx] == c.ids[start]
          // But node = dstidx = end, so start == node or start == dstidx
          // So c.ids[start] == v'.highest_heard[dstidx] > c.ids[dstidx]
          // But c.ids[start] == v'.highest_heard[dstidx], so need c.ids[start] > c.ids[dstidx]
          // But start == node == dstidx, so c.ids[start] == c.ids[dstidx]
          // So v'.highest_heard[dstidx] == c.ids[dstidx]
          // But OnChordHeardDominatesId requires v'.highest_heard[node] > c.ids[node]
          // So this can only happen if c.ids[dstidx] > c.ids[dstidx], which is impossible
          // Therefore, IsChord(c, v', start, end) cannot be newly created at dstidx == end
          // So the only way for IsChord to hold is if it already held before, so v.highest_heard[node] > c.ids[node]
          // So v'.highest_heard[node] >= v.highest_heard[node] > c.ids[node]
          assert v'.highest_heard[node] >= v.highest_heard[node];
          assert v.highest_heard[node] > c.ids[node];
        }
      } else {
        // node != dstidx, so v'.highest_heard[node] == v.highest_heard[node]
        assert v.highest_heard[node] > c.ids[node];
      }
    }
  }

  // 3. Safety(c, v')
  forall i, j | IsLeader(c, v', i) && IsLeader(c, v', j) ensures i == j {
    // IsLeader(c, v', i): v'.highest_heard[i] == c.ids[i]
    // IsLeader(c, v', j): v'.highest_heard[j] == c.ids[j]
    // But highest_heard values are only ever set to c.ids[k] for some k, and ids are unique
    // Suppose i != j, then c.ids[i] != c.ids[j], but v'.highest_heard[i] == c.ids[i] and v'.highest_heard[j] == c.ids[j]
    // But only one process can have its highest_heard equal to its own id, since only one id can be the maximum
    // But to be a leader, v'.highest_heard[i] == c.ids[i], and v'.highest_heard[j] == c.ids[j]
    // But only one process can have its own id as the maximum
    // By Inv(c, v), Safety(c, v) holds, and the only way for v'.highest_heard[i] == c.ids[i] is if v.highest_heard[i] == c.ids[i] or v.highest_heard[i] < c.ids[i] and message == c.ids[i]
    // But since ids are unique, only one process can have this property
    // Therefore, i == j
    assert i == j;
  }
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
  // By definition of Inv
  assert Safety(c, v);
}

function abs(a: real) : real {if a>0.0 then a else -a}
