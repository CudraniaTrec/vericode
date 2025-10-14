
function Average (a: int, b: int): int 
{
    (a + b) / 2
}

method TripleConditions(x: int) returns (r: int) 
ensures r == 3 * x
{   
    r := 3 * x;
    assert r == 3 * x;
}

method Triple' (x: int) returns (r: int) 
    ensures Average(r, 3 * x) == 3 * x
    ensures r == 3 * x
{
    r:= 3 * x;
    assert r == 3 * x;
    assert Average(r, 3 * x) == 3 * x;
}


method ProveSpecificationsEquivalent(x: int) {
    var result1 := TripleConditions(x);
    var result2 := Triple'(x);
    assert result1 == 3 * x;
    assert result2 == 3 * x;
    assert Average(result2, 3 * x) == 3 * x;
}

function abs(a: real) : real {if a>0.0 then a else -a}
