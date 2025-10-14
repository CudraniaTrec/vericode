// Dafny Code

method IsNonPrime(n: nat) returns (nonPrime: bool)
    ensures nonPrime == (n < 2 || exists k: nat :: 2 <= k < n && n % k == 0)
{
    if n < 2 {
        nonPrime := true;
        return;
    }
    var found := false;
    var k := 2;
    while k < n
        invariant 2 <= k <= n
        invariant !found ==> forall j: nat :: 2 <= j < k ==> n % j != 0
        decreases n - k
    {
        if n % k == 0 {
            found := true;
            break;
        }
        k := k + 1;
    }
    nonPrime := found;
}