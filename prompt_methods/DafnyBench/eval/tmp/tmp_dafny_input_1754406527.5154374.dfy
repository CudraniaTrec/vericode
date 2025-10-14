
method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    var s' : string := [];
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (s[j] == ' ' ==> s'[j] == ch) && (s[j] != ' ' ==> s'[j] == s[j])
    {
        if s[i] == ' '
        {
            s' := s' + [ch];
            assert s'[i] == ch;
        }
        else 
        {
            s' := s' + [s[i]];
            assert s'[i] == s[i];
        }
        i := i + 1;
    }
    assert |s'| == |s|;
    assert forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> s'[i] == ch) && (s[i] != ' ' ==> s'[i] == s[i]);
    return s';
}

function abs(a: real) : real {if a>0.0 then a else -a}
