
method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{
    result := false;
    var found: bool := false;
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result ==> found
        invariant found <==> exists j :: 0 <= j < i && s[j] == k
        invariant !found ==> forall j :: 0 <= j < i ==> s[j] != k
    {
        if s[i] == k {
            result := true;
            found := true;
            break;
        }
        i := i + 1;
    }
    if !result {
        assert forall j :: 0 <= j < |s| ==> s[j] != k;
    }
    assert result <==> (exists j :: 0 <= j < |s| && s[j] == k);
}

function abs(a: real) : real {if a>0.0 then a else -a}
