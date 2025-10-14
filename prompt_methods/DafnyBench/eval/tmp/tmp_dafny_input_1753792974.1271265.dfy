
method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
{
    if |sequences| == 0 {
        return true;
    }

    var firstLength := |sequences[0]|;
    result := true;

    var i: int := 1;
    while i < |sequences|
        invariant 1 <= i <= |sequences|
        invariant result ==> forall j :: 0 <= j < i ==> |sequences[j]| == firstLength
        invariant !result ==> exists k :: 1 <= k < i && |sequences[k]| != firstLength
    {
        if |sequences[i]| != firstLength {
            result := false;
            break;
        }
        i := i + 1;
    }
    // After the loop:
    // If result is true, then all |sequences[j]| == firstLength for 0 <= j < i, and i == |sequences| or result was set to false
    // If result is false, then there exists k with 1 <= k < i and |sequences[k]| != firstLength
    assert result ==> forall j :: 0 <= j < |sequences| ==> |sequences[j]| == firstLength;
    assert !result ==> exists k :: 1 <= k < |sequences| && |sequences[k]| != firstLength;
}

function abs(a: real) : real {if a>0.0 then a else -a}
