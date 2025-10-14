// Dafny Code

method SeqBVXor(seq1: seq<bv8>, seq2: seq<bv8>) returns (result: seq<bv8>)
    requires |seq1| == |seq2|
    ensures |result| == |seq1|
    ensures forall i :: 0 <= i < |seq1| ==> result[i] == seq1[i] ^ seq2[i]
{
    var temp := [];
    var n := |seq1|;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |temp| == i
        invariant forall j :: 0 <= j < i ==> temp[j] == seq1[j] ^ seq2[j]
    {
        temp := temp + [seq1[i] ^ seq2[i]];
        i := i + 1;
    }
    result := temp;
}