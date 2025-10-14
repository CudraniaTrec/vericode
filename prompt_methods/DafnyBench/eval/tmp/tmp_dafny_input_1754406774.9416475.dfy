
method ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    var found: bool := false;
    var idx: int := 0;
    while idx < |s|
        invariant 0 <= idx <= |s|
        invariant !found ==> (forall j :: 0 <= j < idx ==> s[j] != 'z' && s[j] != 'Z')
        invariant found ==> (exists j :: 0 <= j < idx && (s[j] == 'z' || s[j] == 'Z'))
        invariant result == found
    {
        if s[idx] == 'z' || s[idx] == 'Z' {
            found := true;
            result := true;
            break;
        }
        idx := idx + 1;
    }
    if !found {
        result := false;
    }
    assert result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'));
}

function abs(a: real) : real {if a>0.0 then a else -a}
