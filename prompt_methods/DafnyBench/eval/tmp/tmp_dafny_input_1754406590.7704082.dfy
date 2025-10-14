method AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
    assert ascii == c as int;
}
function abs(a: real) : real {if a>0.0 then a else -a}
