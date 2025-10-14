method ContainsSequence(seqs: seq<seq<int>>, target: seq<int>) returns (found: bool)
{
    found := false;
    var i := 0;
    while i < |seqs| && !found
        decreases |seqs| - i
    {
        if seqs[i] == target {
            found := true;
        }
        i := i + 1;
    }
}