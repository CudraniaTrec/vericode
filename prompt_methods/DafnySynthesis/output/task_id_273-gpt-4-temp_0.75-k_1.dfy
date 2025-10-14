method SubtractSequences(s1: seq<int>, s2: seq<int>) returns (result: seq<int>)
    requires |s1| == |s2|
    ensures |result| == |s1|
    ensures forall i :: 0 <= i < |s1| ==> result[i] == s1[i] - s2[i]
{
    result := seq i | 0 <= i < |s1| :: s1[i] - s2[i];
}