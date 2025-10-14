method CountPrimesLessThan(n: nat) returns (count: nat)
    ensures 0 <= count <= n
    ensures forall k: nat :: 2 <= k < n ==> (IsPrime(k) ==> exists _ : nat :: count > 0)
{
    if n <= 2 {
        return 0;
    }

    var isPrime := new bool[n];
    var i: nat := 0;
    while i < n
        invariant 0 <= i <= n
        invariant isPrime.Length == n
    {
        if i < 2 {
            isPrime[i] := false;
        } else {
            isPrime[i] := true;
        }
        i := i + 1;
    }

    var p: nat := 2;
    while p * p < n
        invariant 2 <= p <= n
        invariant forall k: nat :: 2 <= k < p ==> isPrime[k] ==> IsPrime(k)
    {
        if isPrime[p] {
            var j: nat := p * p;
            while j < n
                invariant p * p <= j <= n
            {
                isPrime[j] := false;
                j := j + p;
            }
        }
        p := p + 1;
    }

    count := 0;
    i := 2;
    while i < n
        invariant 2 <= i <= n
        invariant 0 <= count <= i - 2
        invariant forall k: nat :: 2 <= k < i ==> isPrime[k] ==> IsPrime(k)
    {
        if isPrime[i] {
            count := count + 1;
        }
        i := i + 1;
    }
}

// Helper predicate for primality
predicate IsPrime(k: nat)
    requires k >= 2
{
    forall d: nat :: 2 <= d < k ==> k % d != 0
}