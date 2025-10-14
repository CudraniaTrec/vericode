method RemoveAt(a: array<int>, k: int) returns (res: array<int>)
    requires a != null
    requires 0 <= k < a.Length
    ensures res != null
    ensures res.Length == a.Length - 1
    ensures forall i :: 0 <= i < k ==> res[i] == a[i]
    ensures forall i :: k <= i < res.Length ==> res[i] == a[i + 1]
{
    var n := a.Length;
    res := new int[n - 1];
    // Copy elements before k
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> res[j] == a[j]
    {
        res[i] := a[i];
        i := i + 1;
    }
    // Copy elements after k
    i := k;
    while i < n - 1
        invariant k <= i <= n - 1
        invariant forall j :: 0 <= j < k ==> res[j] == a[j]
        invariant forall j :: k <= j < i ==> res[j] == a[j + 1]
    {
        res[i] := a[i + 1];
        i := i + 1;
    }
}