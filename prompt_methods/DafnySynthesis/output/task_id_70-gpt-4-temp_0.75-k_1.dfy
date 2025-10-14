//Dafny Code

method AllSequencesHaveEqualLength(seqs: seq<seq<int>>): bool
{
    if |seqs| == 0 || |seqs| == 1 {
        return true;
    }
    var len := |seqs[0]|;
    var i := 1;
    while i < |seqs|
        invariant 1 <= i <= |seqs|
        invariant forall j :: 0 <= j < i ==> |seqs[j]| == len
    {
        if |seqs[i]| != len {
            return false;
        }
        i := i + 1;
    }
    return true;
}