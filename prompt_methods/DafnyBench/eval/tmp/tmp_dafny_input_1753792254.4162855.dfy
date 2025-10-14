method ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result ==> (exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z'))
        invariant !result ==> (forall j :: 0 <= j < i ==> s[j] != 'z' && s[j] != 'Z')
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            break;
        }
        i := i + 1;
    }
    if !result {
        assert forall j :: 0 <= j < |s| ==> s[j] != 'z' && s[j] != 'Z';
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
