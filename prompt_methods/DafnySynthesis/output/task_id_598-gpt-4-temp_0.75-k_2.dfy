method IsArmstrong(n: int) returns (res: bool)
        requires n >= 0
        ensures res <==> (var digits := NumDigits(n); n == SumOfPowerOfDigits(n, digits))
    {
        var digits := NumDigits(n);
        var sum := SumOfPowerOfDigits(n, digits);
        res := sum == n;
    }

    function method NumDigits(n: int): int
        requires n >= 0
        ensures NumDigits(n) > 0
    {
        if n == 0 then 1 else 1 + NumDigits(n / 10)
    }

    function method Power(base: int, exp: int): int
        requires exp >= 0
        decreases exp
    {
        if exp == 0 then 1 else base * Power(base, exp - 1)
    }

    function method SumOfPowerOfDigits(n: int, digits: int): int
        requires n >= 0 && digits > 0
        decreases n
    {
        if n == 0 then 0 else Power(n % 10, digits) + SumOfPowerOfDigits(n / 10, digits)
    }