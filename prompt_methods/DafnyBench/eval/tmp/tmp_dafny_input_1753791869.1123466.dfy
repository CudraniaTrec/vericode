method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    // |s| is always non-negative
    assert |s| >= 0;
    count := |s|;
    assert count == |s|;
    assert count >= 0;
}
function abs(a: real) : real {if a>0.0 then a else -a}
