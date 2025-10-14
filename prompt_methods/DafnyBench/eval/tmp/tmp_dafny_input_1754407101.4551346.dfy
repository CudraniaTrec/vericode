method NthOctagonalNumber(n: int) returns (octagonalNumber: int)
    requires n >= 0
    ensures octagonalNumber == n * (3 * n - 2)
{
    // n >= 0 by precondition
    assert n >= 0;
    octagonalNumber := n * (3 * n - 2);
    assert octagonalNumber == n * (3 * n - 2);
}
function abs(a: real) : real {if a>0.0 then a else -a}
