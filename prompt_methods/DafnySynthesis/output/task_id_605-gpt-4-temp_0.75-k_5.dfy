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
    var d := 3;
    while d * d <= n
        invariant 2 < d <= n+1
        decreases n - d
    {
        if n % d == 0 {
            prime := false;
            return;
        }
        d := d + 2;
    }
    prime := true;
}