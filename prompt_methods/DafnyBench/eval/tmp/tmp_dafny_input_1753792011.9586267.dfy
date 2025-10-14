method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{
    // |l| > 0 because 0 <= index < |l|
    assert |l| > 0;
    // (index - n + |l|) % |l| is in 0 .. |l|-1
    assert 0 <= (index - n + |l|) % |l| < |l|;
    element := l[(index - n + |l|) % |l|];
    assert element == l[(index - n + |l|) % |l|];
}
function abs(a: real) : real {if a>0.0 then a else -a}
