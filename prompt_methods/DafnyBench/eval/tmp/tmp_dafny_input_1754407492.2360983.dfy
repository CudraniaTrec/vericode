method CenteredHexagonalNumber(n: nat) returns (result: nat)
    requires n >= 0
    ensures result == 3 * n * (n - 1) + 1
{
    // n is a natural number, so n >= 0
    assert n >= 0;
    // Compute the centered hexagonal number
    result := 3 * n * (n - 1) + 1;
    // Postcondition holds by direct assignment
    assert result == 3 * n * (n - 1) + 1;
}
function abs(a: real) : real {if a>0.0 then a else -a}
