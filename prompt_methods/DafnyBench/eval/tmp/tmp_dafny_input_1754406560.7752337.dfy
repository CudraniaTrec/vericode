method Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
{
    // The result sequence must have length 2 and contain b at index 0 and a at index 1
    result := [b, a];
    assert |result| == 2;
    assert result[0] == b;
    assert result[1] == a;
}
function abs(a: real) : real {if a>0.0 then a else -a}
