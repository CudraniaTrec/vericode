
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
{
    result := false;
    var i := 2;
    while i <= n/2
        invariant 2 <= i <= n/2 + 1
        invariant !result
        invariant forall k :: 2 <= k < i ==> n % k != 0
    {
        if n % i == 0
        {
            assert 2 <= i < n;
            result := true;
            break;
        }
        i := i + 1;
    }
    assert result ==> (exists k :: 2 <= k < n && n % k == 0);
    assert !result ==> (forall k :: 2 <= k < n ==> n % k != 0);
}

function abs(a: real) : real {if a>0.0 then a else -a}
