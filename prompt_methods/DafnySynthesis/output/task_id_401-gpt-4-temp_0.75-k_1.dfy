//Dafny Code

method IndexWiseAddNestedSequences(seq1: seq<seq<int>>, seq2: seq<seq<int>>): seq<seq<int>>
    requires |seq1| == |seq2|
    requires forall i :: 0 <= i < |seq1| ==> |seq1[i]| == |seq2[i]|
    ensures |IndexWiseAddNestedSequences(seq1, seq2)| == |seq1|
    ensures forall i :: 0 <= i < |seq1| ==> |IndexWiseAddNestedSequences(seq1, seq2)[i]| == (seq j | 0 <= j < |seq1[i]| :: seq1[i][j] + seq2[i][j])
{
    var result := [];
    var n := |seq1|;
    var m:int;
    var inner:seq<int>;
    var inner1:seq<int>;
    var inner2:seq<int>;
    var res_inner:seq<int>;
    var i:int := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> |result[k]| == |seq1[k]|
        invariant forall k :: 0 <= k < i ==> result[k] == (seq j | 0 <= j < |seq1[k]| :: seq1[k][j] + seq2[k][j])
    {
        inner1 := seq1[i];
        inner2 := seq2[i];
        m := |inner1|;
        res_inner := [];
        var j:int := 0;
        while j < m
            invariant 0 <= j <= m
            invariant |res_inner| == j
            invariant forall l :: 0 <= l < j ==> res_inner[l] == inner1[l] + inner2[l]
        {
            res_inner := res_inner + [inner1[j] + inner2[j]];
            j := j + 1;
        }
        result := result + [res_inner];
        i := i + 1;
    }
    return result;
}