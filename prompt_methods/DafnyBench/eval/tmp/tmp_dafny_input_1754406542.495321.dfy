method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    // |s| is always non-negative
    count := |s|;
    assert count >= 0;
    assert count == |s|;
}
function abs(a: real) : real {if a>0.0 then a else -a}
