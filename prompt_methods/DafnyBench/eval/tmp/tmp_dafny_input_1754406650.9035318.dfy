method StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
{
    assert |s| > 0;
    result := s[0] == s[|s| - 1];
    assert result <==> s[0] == s[|s| - 1];
}
function abs(a: real) : real {if a>0.0 then a else -a}
