//Dafny Code

method Squares(arr: array<int>) returns (result: array<int>)
    requires arr != null
    ensures result != null && result.Length == arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> result[i] == arr[i] * arr[i]
{
    var n := arr.Length;
    result := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result != null && result.Length == n
        invariant forall j :: 0 <= j < i ==> result[j] == arr[j] * arr[j]
    {
        result[i] := arr[i] * arr[i];
        i := i + 1;
    }
}