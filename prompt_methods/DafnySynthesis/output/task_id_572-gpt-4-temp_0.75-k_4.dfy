// Dafny Code

method RemoveDuplicates(arr: array<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| && i != j ==> result[i] != result[j]
    ensures forall x :: x in result <==> x in arr[..]
{
    var seen := map x: int {:auto_trigger} | false;
    var output := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < |output| ==> output[j] in arr[..i]
        invariant forall k :: 0 <= k < i ==> arr[k] in output <==> seen[arr[k]]
        invariant forall j, k :: 0 <= j < |output| && 0 <= k < |output| && j != k ==> output[j] != output[k]
        decreases arr.Length - i
    {
        if !seen[arr[i]] {
            output := output + [arr[i]];
            seen := seen[arr[i] := true];
        }
        i := i + 1;
    }
    result := output;
}