
method arrayUpToN(n: int) returns (a: array<int>)
    requires n >= 0
    ensures a.Length == n
    ensures forall j :: 0 < j < n ==> a[j] >= 0
    ensures forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
{
    var i := 0;
    a := new int[n];
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> a[j] == j
        invariant forall j :: 0 <= j < i ==> a[j] >= 0
        invariant forall j, k :: 0 <= j <= k < i ==> a[j] <= a[k]
        invariant a.Length == n
    {
        a[i] := i;
        assert a[i] == i;
        i := i + 1;
    }
    assert a.Length == n;
    assert forall j :: 0 < j < n ==> a[j] >= 0;
    assert forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k];
}

function abs(a: real) : real {if a>0.0 then a else -a}
