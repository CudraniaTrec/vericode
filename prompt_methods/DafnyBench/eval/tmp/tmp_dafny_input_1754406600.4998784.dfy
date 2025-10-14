method NthDecagonalNumber(n: int) returns (decagonal: int)
    requires n >= 0
    ensures decagonal == 4 * n * n - 3 * n
{
    // No loop, so no loop invariants needed
    // Strongest assertion before assignment
    assert n >= 0;
    decagonal := 4 * n * n - 3 * n;
    // Assert postcondition
    assert decagonal == 4 * n * n - 3 * n;
}
function abs(a: real) : real {if a>0.0 then a else -a}
