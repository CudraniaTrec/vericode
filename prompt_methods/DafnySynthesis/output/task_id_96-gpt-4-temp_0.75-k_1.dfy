method NumDivisors(n: int) returns (count: int)
    requires n > 0
    ensures count == |set d | 1 <= d <= n && n % d == 0|
{
    count := 0;
    var i := 1;
    while i * i <= n
        invariant 1 <= i
        invariant i * i <= n + 1
        invariant count == |set d | 1 <= d < i && n % d == 0| + |set d | 1 <= d < i && n % (n / d) == 0 && n / d != d|
    {
        if n % i == 0 {
            if i * i == n {
                count := count + 1;
            } else {
                count := count + 2;
            }
        }
        i := i + 1;
    }
}