
method AllCharactersSame(s: string) returns (result: bool)
    ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
    ensures !result ==> (|s| > 1) && (exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j])
{
    if |s| <= 1 {
        return true;
    }

    var firstChar := s[0];
    result := true;

    var i: int := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant result ==> forall j :: 0 <= j < i ==> s[j] == firstChar
        invariant !result ==> (exists k :: 1 <= k < i && s[k] != firstChar)
    {
        if s[i] != firstChar {
            result := false;
            break;
        }
        i := i + 1;
    }
    // Post-loop assertion
    assert result ==> forall j :: 0 <= j < |s| ==> s[j] == firstChar;
    assert !result ==> (exists k :: 1 <= k < |s| && s[k] != firstChar);
}

function abs(a: real) : real {if a>0.0 then a else -a}
