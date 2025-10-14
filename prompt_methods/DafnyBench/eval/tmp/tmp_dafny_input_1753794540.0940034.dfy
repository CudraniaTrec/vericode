
function Average(a: int, b: int): int 
{
    (a + b) / 2
}

ghost method Triple(x: int) returns (r: int)
    ensures r == 3 * x
{
    r := Average(2 * x, 4 * x);
    assert r == (2 * x + 4 * x) / 2;
    assert r == (6 * x) / 2;
    assert r == 3 * x;
}

method Triple1(x: int) returns (r: int)
    ensures r == 3 * x
{
    var y := 2 * x; 
    r := x + y;
    assert y == 2 * x;
    assert r == x + 2 * x;
    assert r == 3 * x;
    ghost var a, b := DoubleQuadruple(x);
    assert a == 2 * x && b == 4 * x;
}

ghost method DoubleQuadruple(x: int) returns (a: int, b: int)
    ensures a == 2 * x && b == 4 * x
{
    a := 2 * x;
    assert a == 2 * x;
    b := 2 * a;
    assert b == 2 * (2 * x);
    assert b == 4 * x;
}

function F(): int {
29
}

method M() returns (r: int) 
ensures r == 29
{
    r := 29;
    assert r == 29;
}

method Caller() {
    var a := F();
    assert a == 29;
    var b := M();
    assert b == 29;
}

method MyMethod(x: int) returns (y: int)
    requires 10 <= x
    ensures 25 <= y
{ 
    var a, b;
    a := x + 3;
    assert a == x + 3;

    if x < 20 {
        b := 32 - x;
        assert b == 32 - x;
        assert x < 20;
        assert 10 <= x < 20;
        assert 13 <= a < 23;
        assert 12 <= b <= 22;
        y := a + b;
        assert y == (x + 3) + (32 - x);
        assert y == 35;
        assert 25 <= y;
    } else {
        b := 16;
        assert b == 16;
        assert x >= 20;
        assert a == x + 3;
        assert a >= 23;
        y := a + b;
        assert y == (x + 3) + 16;
        assert y == x + 19;
        assert x >= 20 ==> y >= 39;
        assert y >= 39;
        assert 25 <= y;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
