method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{
    result := false;
    var found: bool := false;
    var idx: int := 0;
    while idx < |seq1|
        invariant 0 <= idx <= |seq1|
        invariant result == (exists j :: 0 <= j < idx && seq1[j] in seq2)
    {
        if seq1[idx] in seq2 {
            result := true;
            break;
        }
        idx := idx + 1;
    }
    assert result == (exists i :: 0 <= i < |seq1| && seq1[i] in seq2);
}
function abs(a: real) : real {if a>0.0 then a else -a}
