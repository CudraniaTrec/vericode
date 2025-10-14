method AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    // c is a char, so c as int is in 0..65535
    assert 0 <= c as int <= 65535;
    ascii := c as int;
    assert ascii == c as int;
}
function abs(a: real) : real {if a>0.0 then a else -a}
