function Factorial(n: int): int
    requires n >= 0
    ensures 0 <= Factorial(n)
    {
        if n == 0 then 1
        else n * Factorial(n-1)
    }

method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
{
    var lastDigit := n % 10;
    assert 0 <= lastDigit < 10;
    assert lastDigit == n % 10;
    fact := Factorial(lastDigit);
    assert fact == Factorial(n % 10);
}
function abs(a: real) : real {if a>0.0 then a else -a}
