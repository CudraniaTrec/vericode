// Dafny Code

method AllSequencesHaveEqualLength(seqs: seq<seq<int>>) returns (equalLength: bool)
{
    if |seqs| == 0 || |seqs| == 1 {
        // Zero or one sequence: trivially equal length
        equalLength := true;
        return;
    }
    var expectedLength := |seqs[0]|;
    var i := 1;
    while i < |seqs|
        invariant 1 <= i <= |seqs|
        invariant forall j :: 0 <= j < i ==> |seqs[j]| == expectedLength
    {
        if |seqs[i]| != expectedLength {
            equalLength := false;
            return;
        }
        i := i + 1;
    }
    equalLength := true;
}