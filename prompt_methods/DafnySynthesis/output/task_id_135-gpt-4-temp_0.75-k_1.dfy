method HexagonalNumber(n: nat) returns (h: nat)
    ensures h == n * (2 * n - 1)
{
    h := n * (2 * n - 1);
}