method ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{
    result := false;
    var found: bool := false;
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result == false ==> (forall j :: 0 <= j < i ==> s[j] != 'z' && s[j] != 'Z')
        invariant result == true ==> (exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z'))
    {
        if s[i] == 'z' || s[i] == 'Z' {
            result := true;
            break;
        }
        i := i + 1;
    }
    // Post-loop assertion to connect loop to postcondition
    assert result <==> (exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z'));
    // If result is still false, then no 'z' or 'Z' was found in s[0..|s|-1]
    if !result {
        assert forall j :: 0 <= j < |s| ==> s[j] != 'z' && s[j] != 'Z';
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
