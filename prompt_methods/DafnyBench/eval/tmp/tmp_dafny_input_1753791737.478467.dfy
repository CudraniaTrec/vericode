method NthHexagonalNumber(n: int) returns (hexNum: int)
    requires n >= 0
    ensures hexNum == n * ((2 * n) - 1)
{
    // n >= 0 by precondition
    assert n >= 0;
    hexNum := n * ((2 * n) - 1);
    assert hexNum == n * ((2 * n) - 1);
}
function abs(a: real) : real {if a>0.0 then a else -a}
