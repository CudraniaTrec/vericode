method SubtractSequences(s1: seq<int>, s2: seq<int>) returns (result: seq<int>)
    requires |s1| == |s2|
    ensures |result| == |s1|
    ensures forall i :: 0 <= i < |result| ==> result[i] == s1[i] - s2[i]
{
    var res := [];
    var n := |s1|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |res| == i
        invariant forall j :: 0 <= j < i ==> res[j] == s1[j] - s2[j]
    {
        res := res + [s1[i] - s2[i]];
        i := i + 1;
    }
    result := res;
}