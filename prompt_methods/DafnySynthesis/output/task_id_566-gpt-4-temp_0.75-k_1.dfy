method SumOfDigits(n: nat) returns (sum: nat)
    ensures sum == SumDigitsSpec(n)
{
    var temp := n;
    sum := 0;
    while temp > 0
        invariant 0 <= temp <= n
        invariant sum + SumDigitsSpec(temp) == SumDigitsSpec(n)
    {
        sum := sum + temp % 10;
        temp := temp / 10;
    }
}

/// Specification function for sum of digits
function method SumDigitsSpec(n: nat): nat
    decreases n
{
    if n < 10 then n else n % 10 + SumDigitsSpec(n / 10)
}