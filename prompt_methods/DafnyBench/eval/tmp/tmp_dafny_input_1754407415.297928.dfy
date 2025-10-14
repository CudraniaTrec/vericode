method CountLists(lists: seq<seq<int>>) returns (count: int)
    ensures count >= 0
    ensures count == |lists|
{
    // |lists| is always non-negative, so count will be as well
    count := |lists|;
    assert count >= 0;
    assert count == |lists|;
}
function abs(a: real) : real {if a>0.0 then a else -a}
