
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
        invariant result ==> forall k :: 0 <= k < i ==> |sequences[k]| == firstLength
        invariant !result ==> exists k :: 1 <= k < i && |sequences[k]| != firstLength
    {
        if |sequences[i]| != firstLength {
            result := false;
            break;
        }
        i := i + 1;
    }
    // Post-loop assertion
    assert result <==> forall k :: 0 <= k < |sequences| ==> |sequences[k]| == firstLength;
    assert result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
