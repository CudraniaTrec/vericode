
method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
{
    result := true;
    var i := 2;
    while i <= n/2
        invariant 2 <= i <= n/2 + 1
        invariant result ==> (forall k :: 2 <= k < i ==> n % k != 0)
        invariant !result ==> (exists k :: 2 <= k < i && n % k == 0)
    {
        if n % i == 0
        {
            result := false;
            break;
        }
        i := i + 1;
    }
    assert result ==> (forall k :: 2 <= k < n ==> n % k != 0);
    assert !result ==> (exists k :: 2 <= k < n && n % k == 0);
}

function abs(a: real) : real {if a>0.0 then a else -a}
