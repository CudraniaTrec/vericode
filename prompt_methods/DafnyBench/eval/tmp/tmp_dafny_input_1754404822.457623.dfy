
function abs(x: int): int
{
    if x < 0 then -x else x
}

method Testing_abs()
{
    var v := abs(3);
    assert v == 3;
    assert abs(-5) == 5;
    assert abs(0) == 0;
}


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

function max(a: int, b: int): int
{
    // Fill in an expression here.
    if a > b then a else b
}
method Testing_max() {
    // Add assertions to check max here.
    assert max(3, 5) == 5;
    assert max(10, -2) == 10;
    assert max(-4, -7) == -4;
    assert max(8, 8) == 8;
}


// Exercise 6:

method Abs(x: int) returns (y: int)
    ensures abs(x) == y
{
    // Then change this body to also use abs.
    y := abs(x);
}


// Ghost
ghost function Double(val:int) : int
{
    2 * val
}

method TestDouble(val: int) returns (val2:int)
    ensures val2 == Double(val)
{
    val2 := 2 * val;
    assert val2 == Double(val);
}

function abs(a: real) : real {if a>0.0 then a else -a}
