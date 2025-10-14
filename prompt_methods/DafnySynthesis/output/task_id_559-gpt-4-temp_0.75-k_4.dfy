// Dafny Code

method MaxSubArraySum(a: array<int>) returns (maxSum: int)
    requires a != null && a.Length > 0
    ensures forall i, j :: 0 <= i <= j < a.Length ==> maxSum >= (sum k | i <= k <= j :: a[k])
    ensures exists i, j :: 0 <= i <= j < a.Length && maxSum == (sum k | i <= k <= j :: a[k])
{
    var n := a.Length;
    var currentMax := a[0];
    var globalMax := a[0];

    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant currentMax == (if exists j :: 0 <= j < i ==> (currentMax == (var x := j; (sum k | x <= k < i :: a[k])) && (forall y :: 0 <= y < i ==> (sum k | y <= k < i :: a[k]) <= currentMax))) else a[0])
        invariant globalMax == (forall x, y :: 0 <= x <= y < i ==> (sum k | x <= k <= y :: a[k]) <= globalMax) &&
                              (exists x, y :: 0 <= x <= y < i && globalMax == (sum k | x <= k <= y :: a[k]))
    {
        currentMax := if currentMax + a[i] > a[i] then currentMax + a[i] else a[i];
        globalMax := if globalMax > currentMax then globalMax else currentMax;
        i := i + 1;
    }
    maxSum := globalMax;
}