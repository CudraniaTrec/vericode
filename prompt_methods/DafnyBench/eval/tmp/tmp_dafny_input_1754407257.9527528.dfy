method NthNonagonalNumber(n: int) returns (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
{
    assert n >= 0;
    assert (7 * n - 5) % 2 == (if n % 2 == 0 then 1 else 0); // 7n-5 is odd iff n is odd
    number := n * (7 * n - 5) / 2;
    assert number == n * (7 * n - 5) / 2;
}
function abs(a: real) : real {if a>0.0 then a else -a}
