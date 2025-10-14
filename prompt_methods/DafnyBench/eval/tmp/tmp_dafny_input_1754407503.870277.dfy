
method MinSecondValueFirst(s: array<seq<int>>) returns (firstOfMinSecond: int)
    requires s.Length > 0
    requires forall i :: 0 <= i < s.Length ==> |s[i]| >= 2
    ensures exists i :: 0 <= i < s.Length && firstOfMinSecond == s[i][0] && 
        (forall j :: 0 <= j < s.Length ==> s[i][1] <= s[j][1])
{
    var minSecondIndex := 0;
    // Invariant: minSecondIndex is always an index in 0..i-1 such that s[minSecondIndex][1] is minimal among s[0..i-1]
    for i := 1 to s.Length
        invariant 1 <= i <= s.Length
        invariant 0 <= minSecondIndex < i
        invariant forall j :: 0 <= j < i ==> s[minSecondIndex][1] <= s[j][1]
    {
        assert 0 <= i < s.Length ==> |s[i]| >= 2; // from precondition
        if s[i][1] < s[minSecondIndex][1]
        {
            minSecondIndex := i;
        }
        assert 0 <= minSecondIndex < i+1;
        assert forall j :: 0 <= j < i+1 ==> s[minSecondIndex][1] <= s[j][1];
    }
    assert 0 <= minSecondIndex < s.Length;
    assert forall j :: 0 <= j < s.Length ==> s[minSecondIndex][1] <= s[j][1];
    firstOfMinSecond := s[minSecondIndex][0];
}

function abs(a: real) : real {if a>0.0 then a else -a}
