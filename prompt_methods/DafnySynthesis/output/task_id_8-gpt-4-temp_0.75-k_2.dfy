//Dafny Code

method Squares(arr: array<int>) returns (result: array<int>)
    requires arr != null
    ensures result != null && result.Length == arr.Length
    ensures forall i :: 0 <= i < arr.Length ==> result[i] == arr[i] * arr[i]
{
    result := new int[arr.Length];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant result != null && result.Length == arr.Length
        invariant forall j :: 0 <= j < i ==> result[j] == arr[j] * arr[j]
    {
        result[i] := arr[i] * arr[i];
        i := i + 1;
    }
}