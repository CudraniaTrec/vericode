method CountPrimes(n: nat) returns (count: nat)
    ensures count == (|set i | 2 <= i < n && IsPrime(i)|)
{
    count := 0;
    var i: nat := 2;
    while i < n
        invariant 2 <= i <= n
        invariant count == (|set j | 2 <= j < i && IsPrime(j)|)
    {
        if IsPrime(i) {
            count := count + 1;
        }
        i := i + 1;
    }
}

// Helper predicate to check if k is prime
predicate IsPrime(k: nat)
    decreases k
{
    k >= 2 &&
    (forall d: nat :: 2 <= d < k ==> k % d != 0)
}