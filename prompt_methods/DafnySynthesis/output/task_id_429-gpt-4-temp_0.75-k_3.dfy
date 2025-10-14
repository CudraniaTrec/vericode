// Dafny Code

method ElementwiseAnd(s1: seq<bool>, s2: seq<bool>) returns (res: seq<bool>)
    requires |s1| == |s2|
    ensures |res| == |s1|
    ensures forall i :: 0 <= i < |res| ==> res[i] == s1[i] && s2[i]
{
    res := seq i := 0 to |s1| - 1 :: s1[i] && s2[i];
}