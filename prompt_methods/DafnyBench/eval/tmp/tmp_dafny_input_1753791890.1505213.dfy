method Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
{
    // The result sequence will have exactly two elements: b and a
    assert true; // No complex invariants needed for this simple method
    result := [b, a];
    assert |result| == 2;
    assert result[0] == b;
    assert result[1] == a;
}
function abs(a: real) : real {if a>0.0 then a else -a}
