//Dafny Code

method RemoveOdds(arr: array<int>) returns (result: array<int>)
    ensures forall i :: 0 <= i < result.Length ==> result[i] % 2 == 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 == 0 ==> exists j :: 0 <= j < result.Length && result[j] == arr[i]
    ensures result.Length == |set i | 0 <= i < arr.Length && arr[i] % 2 == 0|
{
    var count := 0;
    // First, count the number of even numbers
    var n := arr.Length;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= count <= i
        invariant count == |set j | 0 <= j < i && arr[j] % 2 == 0|
    {
        if arr[i] % 2 == 0 {
            count := count + 1;
        }
        i := i + 1;
    }
    result := new int[count];
    var j := 0;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= j <= count
        invariant forall k :: 0 <= k < j ==> result[k] % 2 == 0
        invariant forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> exists l :: 0 <= l < j && result[l] == arr[k]
        invariant j == |set k | 0 <= k < i && arr[k] % 2 == 0|
    {
        if arr[i] % 2 == 0 {
            result[j] := arr[i];
            j := j + 1;
        }
        i := i + 1;
    }
}