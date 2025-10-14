
function Average(a: int, b: int): int 
{
    (a + b) / 2
}

ghost method Triple(x: int) returns (r: int)
    ensures r == 3 * x
{
    // 2*x + 4*x = 6*x, (6*x)/2 = 3*x
    assert Average(2 * x, 4 * x) == 3 * x;
    r := Average(2 * x, 4 * x);
}

method Triple1(x: int) returns (r: int)
    ensures r == 3 * x
{
    var y := 2 * x; 
    r := x + y;
    assert r == 3 * x;
    ghost var a, b := DoubleQuadruple(x);
    assert a == 2 * x && b == 4 * x;
}

ghost method DoubleQuadruple(x: int) returns (a: int, b: int)
    ensures a == 2 * x && b == 4 * x
{
    a := 2 * x;
    b := 2 * a;
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
    assert a >= 13; // since x >= 10

    if x < 20 {
        b := 32 - x;
        assert b > 0;
        assert x + 3 + 32 - x == 35;
        y := a + b;
        assert y == 35;
    } else {
        b := 16;
        assert x >= 20;
        assert a >= 23;
        y := a + b;
        assert y >= 39;
    }
    assert y >= 25;
}

function abs(a: real) : real {if a>0.0 then a else -a}
