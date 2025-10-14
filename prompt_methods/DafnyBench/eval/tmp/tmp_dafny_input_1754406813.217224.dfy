
method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{
    var s' : string := [];
    // Invariant: s' has length i, and for all j < i, s'[j] is correct
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (s[j] == oldChar ==> s'[j] == newChar) && (s[j] != oldChar ==> s'[j] == s[j])
    {
        if s[i] == oldChar
        {
            s' := s' + [newChar];
            assert s'[i] == newChar;
        }
        else 
        {
            s' := s' + [s[i]];
            assert s'[i] == s[i];
        }
    }
    assert |s'| == |s|;
    assert forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> s'[i] == newChar) && (s[i] != oldChar ==> s'[i] == s[i]);
    return s';
}

function abs(a: real) : real {if a>0.0 then a else -a}
