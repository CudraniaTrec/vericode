method NthDecagonalNumber(n: int) returns (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
{
    // No loop or complex computation, but we can add an assert for clarity
    assert n >= 0;
    decagonal := 4 * n * n - 3 * n;
    assert decagonal == 4 * n * n - 3 * n;
}
function abs(a: real) : real {if a>0.0 then a else -a}
