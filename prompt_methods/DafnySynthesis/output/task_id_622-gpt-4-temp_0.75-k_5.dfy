method FindMedianOfTwoSortedLists(A: seq<int>, B: seq<int>) returns (median: real)
    requires |A| == |B|
    requires |A| > 0
    requires forall i :: 0 <= i < |A| - 1 ==> A[i] <= A[i+1]
    requires forall i :: 0 <= i < |B| - 1 ==> B[i] <= B[i+1]
    ensures median == if |A| % 2 == 1
                      then (Merge(A,B))[(|A|+|B|)/2] as real
                      else ((Merge(A,B))[(|A|+|B|)/2 - 1] + (Merge(A,B))[(|A|+|B|)/2]) / 2.0
{
    var n := |A|;
    var i := 0;
    var j := 0;
    var count := 0;
    var m1 := 0;
    var m2 := 0;
    while count <= n
        invariant 0 <= i <= n && 0 <= j <= n
        invariant count == i + j
        decreases n - count
    {
        if i < n && (j >= n || A[i] <= B[j]) {
            m1 := m2;
            m2 := A[i];
            i := i + 1;
        } else {
            m1 := m2;
            m2 := B[j];
            j := j + 1;
        }
        count := count + 1;
    }

    if n % 2 == 1 {
        median := m2 as real;
    } else {
        median := (m1 as real + m2 as real) / 2.0;
    }
}

// Helper function to merge two sorted sequences (for ensures)
function Merge(A: seq<int>, B: seq<int>): seq<int>
    decreases |A| + |B|
{
    if |A| == 0 then B
    else if |B| == 0 then A
    else if A[0] <= B[0] then [A[0]] + Merge(A[1..], B)
    else [B[0]] + Merge(A, B[1..])
}