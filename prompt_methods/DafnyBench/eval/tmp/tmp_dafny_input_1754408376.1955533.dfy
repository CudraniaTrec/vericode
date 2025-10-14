method min(a: array<int>, n : int) returns (min : int)
    requires 0 < n <= a.Length;
    ensures (exists i : int :: 0 <= i && i < n && a[i] == min);
    ensures (forall i : int :: 0 <= i && i < n ==> a[i] >= min);
{
    var i : int;

    min := a[0];
    i := 1;

    while (i < n)
        invariant 1 <= n <= a.Length;
        invariant 1 <= i <= n;
        invariant (exists j :: 0 <= j < i && a[j] == min);
        invariant (forall j :: 0 <= j < i ==> a[j] >= min);
    {
        if (a[i] < min) {
            min := a[i];
        }
        i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
