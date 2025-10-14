// Dafny Code

method IndexWiseAddition2D(seq1: seq<seq<int>>, seq2: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |seq1| == |seq2|
    requires forall i :: 0 <= i < |seq1| ==> |seq1[i]| == |seq2[i]|
    ensures |result| == |seq1|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |seq1[i]|
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> result[i][j] == seq1[i][j] + seq2[i][j]
{
    var temp := [];
    var n := |seq1|;
    var m := if n == 0 then 0 else |seq1[0]|; // assuming all inner sequences are the same length
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |temp| == i
        invariant forall k :: 0 <= k < i ==> |temp[k]| == |seq1[k]|
        invariant forall k, j :: 0 <= k < i && 0 <= j < |seq1[k]| ==> temp[k][j] == seq1[k][j] + seq2[k][j]
    {
        var row := [];
        var rowLen := |seq1[i]|;
        var j := 0;
        while j < rowLen
            invariant 0 <= j <= rowLen
            invariant |row| == j
            invariant forall l :: 0 <= l < j ==> row[l] == seq1[i][l] + seq2[i][l]
        {
            row := row + [seq1[i][j] + seq2[i][j]];
            j := j + 1;
        }
        temp := temp + [row];
        i := i + 1;
    }
    result := temp;
}