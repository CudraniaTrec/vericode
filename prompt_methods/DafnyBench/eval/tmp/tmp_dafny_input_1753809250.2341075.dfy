
class Process {
    var row: nat;
    var curColumn: nat;
    var opsLeft: nat;

    constructor (init_row: nat, initOpsLeft: nat) 
        ensures row == init_row
        ensures opsLeft == initOpsLeft
        ensures curColumn == 0
    {
        row := init_row;
        curColumn := 0;
        opsLeft := initOpsLeft;
    }
}

function sum(s : seq<nat>) : nat
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
{
    if s == [] then 0 else s[0] + sum(s[1..])
}

lemma sum0(s : seq<nat>)
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
  {
    if s == [] {
    } else {
      sum0(s[1..]);
      assert sum(s) == s[0] + sum(s[1..]);
      if sum(s) == 0 {
        assert s[0] == 0;
        assert sum(s[1..]) == 0;
        assert forall i :: 0 <= i < |s[1..]| ==> s[1..][i] == 0;
        assert forall i :: 1 <= i < |s| ==> s[i] == 0;
      }
    }
  }

lemma sum_const(s : seq<nat>, x : nat)
  ensures (forall i :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x 
  {
    if s == [] {
      assert sum(s) == 0;
      assert |s| == 0;
      assert 0 == 0 * x;
    } else {
      assert s[0] == x;
      assert forall i :: 0 <= i < |s[1..]| ==> s[1..][i] == x;
      sum_const(s[1..], x);
      assert sum(s) == s[0] + sum(s[1..]);
      assert sum(s) == x + sum(s[1..]);
      assert sum(s) == x + |s[1..]| * x;
      assert |s| == 1 + |s[1..]|;
      assert sum(s) == |s| * x;
    }
  }

lemma sum_eq(s1 : seq<nat>, s2 : seq<nat>)
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
  ensures sum(s1) == sum(s2)
  {
    if |s1| == 0 {
      assert |s2| == 0;
      assert sum(s1) == 0 && sum(s2) == 0;
    } else {
      assert s1[0] == s2[0];
      assert |s1[1..]| == |s2[1..]|;
      assert forall i :: 0 <= i < |s1[1..]| ==> s1[1..][i] == s2[1..][i];
      sum_eq(s1[1..], s2[1..]);
      assert sum(s1) == s1[0] + sum(s1[1..]);
      assert sum(s2) == s2[0] + sum(s2[1..]);
      assert sum(s1) == sum(s2);
    }
  }

lemma sum_exept(s1 : seq<nat>, s2 : seq<nat>, x : nat, j : nat)
requires |s1| == |s2|
requires j < |s1|
requires forall i :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
requires s1[j] == s2[j] + x
ensures sum(s1) == sum(s2) + x
{
    if s1 == [] {
    } else {
        if j == 0 {
            assert s1[0] == s2[0] + x;
            assert forall i :: 0 <= i < |s1[1..]| ==> i != j-1 ==> s1[1..][i] == s2[1..][i];
            sum_eq(s1[1..], s2[1..]);
            assert sum(s1) == s1[0] + sum(s1[1..]);
            assert sum(s2) == s2[0] + sum(s2[1..]);
            assert sum(s1) == (s2[0] + x) + sum(s2[1..]);
            assert sum(s1) == sum(s2) + x;
        } else {
            assert forall i :: 0 <= i < |s1[1..]| ==> (i != j-1) ==> s1[1..][i] == s2[1..][i];
            assert s1[1..][j-1] == s2[1..][j-1] + x;
            sum_exept(s1[1..], s2[1..], x, j - 1);
            assert sum(s1) == s1[0] + sum(s1[1..]);
            assert sum(s2) == s2[0] + sum(s2[1..]);
            assert s1[0] == s2[0];
            assert sum(s1) == s2[0] + (sum(s2[1..]) + x);
            assert sum(s1) == sum(s2) + x;
        }
    }
}


function calcRow(M : array2<int>, x : seq<int>, row: nat, start_index: nat) : (product: int)
    reads M
    requires M.Length1 == |x|
    requires row < M.Length0
    requires start_index <= M.Length1
    decreases M.Length1 - start_index
{
    if start_index == M.Length1 then
        0
    else
        M[row, start_index] * x[start_index] + calcRow(M, x, row, start_index+1)
}

class MatrixVectorMultiplier
{   

    ghost predicate Valid(M: array2<int>, x: seq<int>, y: array<int>, P: set<Process>, leftOvers : array<nat>)
        reads this, y, P, M, leftOvers
    {
        M.Length0 == y.Length &&
        M.Length1 == |x| &&
        |P| == y.Length &&
        |P| == leftOvers.Length &&

        (forall p, q :: p in P && q in P && p != q ==> p.row != q.row) &&
        (forall p, q :: p in P && q in P ==> p != q) &&
        (forall p :: p in P ==> 0 <= p.row < |P|) &&
        (forall p :: p in P ==> 0 <= p.curColumn <= M.Length1) &&
        (forall p :: p in P ==> 0 <= p.opsLeft <= M.Length1) && 
        (forall p :: p in P ==> y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)) &&
        (forall p :: p in P ==> leftOvers[p.row] == p.opsLeft) &&
        (forall p :: p in P ==> p.opsLeft == M.Length1 - p.curColumn) &&
        (sum(leftOvers[..]) > 0 ==> exists p :: p in P && p.opsLeft > 0)
    }


    constructor (processes: set<Process>, M_: array2<int>, x_: seq<int>, y_: array<int>, leftOvers : array<nat>)
        // Idea here is that we already have a set of processes such that each one is assigned one row.
        // Daphny makes it a ginormous pain in the ass to actually create such a set, so we just assume
        // we already have one.

        //this states that the number of rows and processes are the same, and that there is one process
        //for every row, and that no two processes are the same, nor do any two processes share the same
        //row
        requires (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        requires |processes| == leftOvers.Length 
        requires |processes| == M_.Length0
        requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
        requires (forall p, q :: p in processes && q in processes ==> p != q)
        requires (forall p :: p in processes ==> 0 <= p.row < M_.Length0)

        //initializes process start
        requires (forall p :: p in processes ==> 0 == p.curColumn)
        requires (forall p :: p in processes ==> p.opsLeft == M_.Length1)

        requires (forall i :: 0 <= i < y_.Length ==> y_[i] == 0)
        requires y_.Length == M_.Length0

        requires |x_| == M_.Length1
        requires M_.Length0 > 0
        requires |x_| > 0
        ensures (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        ensures Valid(M_, x_, y_, processes, leftOvers)
    {
        // All requirements are satisfied by the input, nothing to do.
        // Valid is established by the requires clauses.
        assert (forall p :: p in processes ==> y_[p.row] + calcRow(M_, x_, p.row, p.curColumn) == calcRow(M_, x_, p.row, 0));
        assert (forall p :: p in processes ==> leftOvers[p.row] == p.opsLeft);
        assert (forall p :: p in processes ==> p.opsLeft == M_.Length1 - p.curColumn);
        assert (forall p :: p in processes ==> 0 <= p.row < |processes|);
        assert (forall p :: p in processes ==> 0 <= p.curColumn <= M_.Length1);
        assert (forall p :: p in processes ==> 0 <= p.opsLeft <= M_.Length1);
        assert (forall p, q :: p in processes && q in processes && p != q ==> p.row != q.row);
        assert (forall p, q :: p in processes && q in processes ==> p != q);
        assert (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1);
        assert (sum(leftOvers[..]) > 0 ==> exists p :: p in processes && p.opsLeft > 0);
    }

    method processNext(M: array2<int>, x: seq<int>, y: array<int>, P : set<Process>, leftOvers : array<nat>)
        requires Valid(M, x, y, P, leftOvers)
        requires exists p :: (p in P && p.opsLeft > 0)
        requires sum(leftOvers[..]) > 0
        modifies this, y, P, leftOvers
        requires (forall p, q :: p in P && q in P && p != q ==> p.row != q.row)

        ensures Valid(M, x, y, P, leftOvers)
        ensures sum(leftOvers[..]) == sum(old(leftOvers[..])) - 1
    {
        var p :| p in P && p.opsLeft > 0;
        // Strongest possible assertions before update
        assert 0 <= p.row < |P|;
        assert 0 <= p.curColumn < M.Length1;
        assert p.opsLeft > 0;
        assert leftOvers[p.row] == p.opsLeft;
        assert y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0);
        assert p.opsLeft == M.Length1 - p.curColumn;
        var oldCurColumn := p.curColumn;
        var oldOpsLeft := p.opsLeft;
        var oldY := y[p.row];
        var oldLeftOvers := leftOvers[p.row];

        y[p.row] := y[p.row] + M[p.row, p.curColumn] * x[p.curColumn];
        p.opsLeft := p.opsLeft - 1;
        p.curColumn := p.curColumn + 1;
        leftOvers[p.row] := leftOvers[p.row] - 1;

        // Strongest possible assertions after update
        assert p.curColumn == oldCurColumn + 1;
        assert p.opsLeft == oldOpsLeft - 1;
        assert leftOvers[p.row] == oldLeftOvers - 1;
        assert p.opsLeft == M.Length1 - p.curColumn;
        assert leftOvers[p.row] == p.opsLeft;
        assert y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0);

        // For all q != p, nothing changed
        assert forall q :: q in P && q != p ==> y[q.row] + calcRow(M, x, q.row, q.curColumn) == calcRow(M, x, q.row, 0);
        assert forall q :: q in P && q != p ==> leftOvers[q.row] == q.opsLeft;
        assert forall q :: q in P && q != p ==> q.opsLeft == M.Length1 - q.curColumn;

        // For all q, 0 <= q.row < |P|, 0 <= q.curColumn <= M.Length1, 0 <= q.opsLeft <= M.Length1
        assert forall q :: q in P ==> 0 <= q.row < |P|;
        assert forall q :: q in P ==> 0 <= q.curColumn <= M.Length1;
        assert forall q :: q in P ==> 0 <= q.opsLeft <= M.Length1;

        // For all q != p, leftOvers[q.row] unchanged
        assert forall q :: q in P && q != p ==> leftOvers[q.row] == old(leftOvers[q.row]);

        // For all q != p, y[q.row] unchanged
        assert forall q :: q in P && q != p ==> y[q.row] == old(y[q.row]);

        // For all q != p, q.curColumn and q.opsLeft unchanged

        // For all q != p, leftOvers[q.row] == q.opsLeft

        sum_exept(old(leftOvers[..]), leftOvers[..], 1, p.row);
        assert sum(leftOvers[..]) == sum(old(leftOvers[..])) - 1;

        // For all q != p, if old(q.opsLeft) > 0, then q.opsLeft > 0
        // For p, if p.opsLeft > 0 after update, then p in P && p.opsLeft > 0
        // If sum(leftOvers[..]) > 0, then exists p :: p in P && p.opsLeft > 0
        if sum(leftOvers[..]) > 0 {
          assert exists q :: q in P && q.opsLeft > 0;
        }
    }


}

method Run(processes: set<Process>, M: array2<int>, x: array<int>) returns (y: array<int>)
    requires |processes| == M.Length0
    requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
    requires (forall p, q :: p in processes && q in processes ==> p != q)
    requires (forall p :: p in processes ==> 0 <= p.row < M.Length0)

    requires (forall p :: p in processes ==> 0 == p.curColumn)
    requires (forall p :: p in processes ==> p.opsLeft == M.Length1)

    requires x.Length > 0
    requires M.Length0 > 0
    requires M.Length1 == x.Length
    ensures M.Length0 == y.Length
    modifies processes, M, x
{
    var i := 0;
    y := new int[M.Length0](i => 0);

    var leftOvers := new nat[M.Length0](i => M.Length1);

    var mv := new MatrixVectorMultiplier(processes, M, x[..], y, leftOvers);
    while sum(leftOvers[..]) > 0 && exists p :: (p in processes && p.opsLeft > 0)
        invariant 0 <= sum(leftOvers[..]) <= M.Length0 * M.Length1
        invariant (forall i :: 0 <= i < leftOvers.Length ==> 0 <= leftOvers[i] <= M.Length1)
        invariant (forall p :: p in processes ==> 0 <= p.opsLeft <= M.Length1)
        invariant (forall p :: p in processes ==> 0 <= p.curColumn <= M.Length1)
        invariant (forall p :: p in processes ==> p.opsLeft == M.Length1 - p.curColumn)
        invariant (forall p :: p in processes ==> leftOvers[p.row] == p.opsLeft)
        invariant (forall p, q :: p in processes && q in processes && p != q ==> p.row != q.row)
        invariant (forall p, q :: p in processes && q in processes ==> p != q)
        invariant (forall p :: p in processes ==> 0 <= p.row < |processes|)
        invariant (forall p :: p in processes ==> y[p.row] + calcRow(M, x[..], p.row, p.curColumn) == calcRow(M, x[..], p.row, 0))
        invariant (forall p :: p in processes ==> y[p.row] == calcRow(M, x[..], p.row, 0) - calcRow(M, x[..], p.row, p.curColumn))
        invariant |processes| == M.Length0
        invariant leftOvers.Length == M.Length0
        invariant y.Length == M.Length0
        invariant (forall i :: 0 <= i < y.Length ==> y[i] == calcRow(M, x[..], i, 0) - calcRow(M, x[..], i, (M.Length1 - leftOvers[i])))
        decreases sum(leftOvers[..])
    {
        mv.processNext(M, x[..], y, processes, leftOvers);
    }


}

function abs(a: real) : real {if a>0.0 then a else -a}
