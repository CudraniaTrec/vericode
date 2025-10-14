method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{
    var i := 0;
    while (i * i < n)
        invariant 0 <= i <= n + 1
        invariant forall a: int :: 0 <= a < i ==> a * a < n
    {
        i := i + 1;
    }
    assert i * i >= n;
    assert forall a: int :: 0 <= a < i ==> a * a < n;
    return i * i == n;
}
function abs(a: real) : real {if a>0.0 then a else -a}
