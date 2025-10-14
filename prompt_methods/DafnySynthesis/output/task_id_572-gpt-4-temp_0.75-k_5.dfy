// Dafny Code

method RemoveDuplicates(arr: array<int>) returns (result: seq<int>)
    ensures set result == set arr[..]
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var seen := map[];
    var res := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant forall v :: v in set res ==> v in set arr[..i]
        invariant forall j :: 0 <= j < |res| ==> res[j] in set arr[..i]
        invariant forall x :: x in set res ==> seen[x]
        invariant forall x :: seen[x] ==> x in set res
        decreases arr.Length - i
    {
        if !(arr[i] in seen) {
            seen := seen[arr[i] := true];
            res := res + [arr[i]];
        }
        i := i + 1;
    }
    result := res;
}