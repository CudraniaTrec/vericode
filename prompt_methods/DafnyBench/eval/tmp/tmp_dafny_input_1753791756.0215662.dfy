method CountArrays(arrays: seq<array<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |arrays|
{
    // |arrays| is always non-negative
    assert |arrays| >= 0;
    count := |arrays|;
    assert count >= 0;
    assert count == |arrays|;
}
function abs(a: real) : real {if a>0.0 then a else -a}
