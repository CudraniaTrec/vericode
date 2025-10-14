method TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{
    // base, height, length > 0 by preconditions
    assert base > 0;
    assert height > 0;
    assert length > 0;
    // Multiplication of positive integers is positive
    assert base * height > 0;
    assert base * height * length > 0;
    // Division by 2 is safe since numerator > 0
    volume := (base * height * length) / 2;
    assert volume == (base * height * length) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
