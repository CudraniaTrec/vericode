method RemoveAt(a: array<int>, k: int) returns (b: array<int>)
    requires a != null
    requires 0 <= k < a.Length
    ensures b.Length == a.Length - 1
    ensures forall i :: 0 <= i < k ==> b[i] == a[i]
    ensures forall i :: k <= i < b.Length ==> b[i] == a[i+1]
{
    b := new int[a.Length - 1];
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> b[j] == a[j]
    {
        b[i] := a[i];
        i := i + 1;
    }
    while i < b.Length
        invariant k <= i <= b.Length
        invariant forall j :: 0 <= j < k ==> b[j] == a[j]
        invariant forall j :: k <= j < i ==> b[j] == a[j+1]
    {
        b[i] := a[i+1];
        i := i + 1;
    }
}