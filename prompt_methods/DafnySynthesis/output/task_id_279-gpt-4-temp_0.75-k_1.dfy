method NthDecagonalNumber(n: nat) returns (result: nat)
    ensures result == n * (8 * n - 6) / 2
{
    // The nth decagonal number formula: D(n) = n * (8n - 6) / 2
    result := n * (8 * n - 6) / 2;
}