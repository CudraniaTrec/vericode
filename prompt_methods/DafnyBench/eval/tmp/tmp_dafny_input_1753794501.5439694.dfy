
method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures forall i :: 0 <= i < n ==> !P(a[i])
{
    n := 0;
    while n != a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> !P(a[i])
    {
        if P(a[n]) {
            assert 0 <= n < a.Length;
            assert forall i :: 0 <= i < n ==> !P(a[i]);
            return;
        }
        n := n + 1;
    }
    assert n == a.Length;
    assert forall i :: 0 <= i < n ==> !P(a[i]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
