method SubtractArrays(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a != null && b != null
    requires a.Length == b.Length
    ensures result != null && result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] - b[i]
{
    var n := a.Length;
    result := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result != null && result.Length == n
        invariant forall j :: 0 <= j < i ==> result[j] == a[j] - b[j]
    {
        result[i] := a[i] - b[i];
        i := i + 1;
    }
}