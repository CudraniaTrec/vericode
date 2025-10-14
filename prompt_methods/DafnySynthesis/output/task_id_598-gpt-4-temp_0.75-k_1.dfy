// Dafny Code

method IsArmstrong(n: int) returns (res: bool)
    ensures res <==> (n >= 0 && n == SumOfPowers(n))
{
    if n < 0 {
        res := false;
        return;
    }
    var sum := SumOfPowers(n);
    res := sum == n;
}

function NumberOfDigits(n: int): int
    requires n >= 0
{
    if n < 10 then 1 else 1 + NumberOfDigits(n / 10)
}

function SumOfPowers(n: int): int
    requires n >= 0
{
    if n < 10 then n
    else Power(n % 10, NumberOfDigits(n)) + SumOfPowers(n / 10)
}

function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1
    else base * Power(base, exp - 1)
}