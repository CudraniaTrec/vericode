// Dafny Code

method PairwiseNeighborSum(s: seq<int>) returns (result: seq<int>)
    ensures |result| == if |s| == 0 then 0 else |s| - 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == s[i] + s[i+1]
{
    result := [];
    if |s| < 2 {
        return;
    }
    var i := 0;
    while i < |s| - 1
        invariant 0 <= i <= |s| - 1
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == s[j] + s[j+1]
    {
        result := result + [s[i] + s[i+1]];
        i := i + 1;
    }
}