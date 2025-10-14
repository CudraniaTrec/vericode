method Triple(x: int) returns (r: int)
{
    var y := 2 * x;
    assert y == 2 * x;
    r := x + y;
    assert r == 3 * x;
}

method TripleIf(x: int) returns (r: int) {
    if (x == 0) {
        r := 0;
        assert r == 3 * x;
    } else {
        var y := 2 * x;
        assert y == 2 * x;
        r := x + y;
        assert r == 3 * x;
    }
}

method TripleOver(x: int) returns (r: int) {
    if {
        case x < 18 =>
        var a, b := 2 * x, 4 * x;
        assert a == 2 * x && b == 4 * x;
        r := (a + b) / 2;
        assert r == 3 * x;
        case 0 <= x =>
        var y:= 2 * x;
        assert y == 2 * x;
        r := x + y;
        assert r == 3 * x;
    }
}

method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
    var y := x / 2;
    assert x % 2 == 0;
    assert y * 2 == x;
    r := 6 * y;
    assert r == 3 * x;
}

method Caller() {
    var t := TripleConditions(18);
    assert t == 54;
}
function abs(a: real) : real {if a>0.0 then a else -a}
