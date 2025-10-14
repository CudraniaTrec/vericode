method IsPrime(n: int) returns (prime: bool)
{
    if n <= 1 {
        prime := false;
        return;
    }
    if n == 2 {
        prime := true;
        return;
    }
    if n % 2 == 0 {
        prime := false;
        return;
    }
    var i: int := 3;
    while i * i <= n
        invariant 2 <= i <= n
        invariant forall j :: 2 <= j < i ==> n % j != 0
    {
        if n % i == 0 {
            prime := false;
            return;
        }
        i := i + 2;
    }
    prime := true;
}