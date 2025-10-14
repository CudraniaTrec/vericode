method TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{
    // n >= 0 by precondition
    assert n * (n + 1) * (n + 2) % 6 == 0; // The product is always divisible by 6 for n >= 0
    t := n * (n + 1) * (n + 2) / 6;
    assert t == n * (n + 1) * (n + 2) / 6; // Postcondition
}
function abs(a: real) : real {if a>0.0 then a else -a}
