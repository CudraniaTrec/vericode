// Dafny Code

method GetLucidNumbers(n: int) returns (lucidNumbers: seq<int>)
    ensures 0 <= n ==> forall i :: 0 <= i < |lucidNumbers| ==> 1 <= lucidNumbers[i] <= n
    ensures lucidNumbers == [x | x := 1 to n, IsLucid(x)]
{
    var L := set x | 1 <= x <= n && IsLucid(x);
    lucidNumbers := [];
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant lucidNumbers == [x | x := 1 to i-1, IsLucid(x)]
    {
        if IsLucid(i) {
            lucidNumbers := lucidNumbers + [i];
        }
        i := i + 1;
    }
}

/// A lucid number is any integer that can be expressed as p^a + q^b for nonnegative integers a, b,
/// where p and q are distinct prime numbers (often 2 and 3).
/// Here we use 2 and 3 as the base primes.
function IsLucid(x: int): bool
{
    exists a, b :: 0 <= a && 0 <= b && x == Power(2, a) + Power(3, b)
}

/// Power function for non-negative exponents
function method Power(base: int, exp: int): int
    requires 0 <= exp
{
    if exp == 0 then 1 else base * Power(base, exp-1)
}