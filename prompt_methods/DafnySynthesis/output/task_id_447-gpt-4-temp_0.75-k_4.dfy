//Dafny Code

method CubesOfArray(a: array<int>) returns (result: array<int>)
    requires a != null
    ensures result != null && result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[i] * a[i] * a[i]
{
    var n := a.Length;
    result := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result != null && result.Length == n
        invariant forall j :: 0 <= j < i ==> result[j] == a[j] * a[j] * a[j]
    {
        result[i] := a[i] * a[i] * a[i];
        i := i + 1;
    }
}