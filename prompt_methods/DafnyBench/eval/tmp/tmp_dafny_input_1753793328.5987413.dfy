method CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{
    // n >= 0 by precondition
    assert n * (n - 1) >= 0;
    assert 3 * n * (n - 1) + 1 >= 1;
    result := 3 * n * (n - 1) + 1;
    assert result == 3 * n * (n - 1) + 1;
}
function abs(a: real) : real {if a>0.0 then a else -a}
