method NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    // n >= 0
    assert n >= 0;
    // number will be assigned as per the formula
    number := n * (7 * n - 5) / 2;
    // Postcondition: number == n * (7 * n - 5) / 2
    assert number == n * (7 * n - 5) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
