
predicate sorted(a: seq<nat>)
{
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method Isort(a: array<nat>)
    modifies a
    ensures sorted(a[..])
{
    if a.Length == 0 {
        return;
    }

    var n := 1;
    while n < a.Length
        invariant 1 <= n <= a.Length
        invariant sorted(a[..n])
        invariant multiset(a[..n]) + multiset(a[n..]) == multiset(old(a[..]))
    {
        var curr := a[n];

        // 1. Find our pivot position k, the location where we should insert the
        // current value.
        var k := n;
        while k > 0 && a[k-1] > curr
            invariant 0 <= k <= n
            invariant forall i :: k <= i < n ==> a[i] > curr
            invariant forall i :: 0 <= i < k ==> a[i] <= curr
            invariant sorted(a[..n])
        {
            k := k-1;
        }

        // 2. Shift all elements between k and n to the right by one.
        var j := n - 1;
        while j >= k
            invariant k-1 <= j < n
            invariant forall i :: j+1 <= i < n ==> a[i] > curr
            invariant forall i :: 0 <= i < k ==> a[i] <= curr
            invariant sorted(a[..k])
            invariant sorted(a[j+1..n])
            decreases j
        {
            a[j+1] := a[j];
            j := j-1;
        }

        // 3. Put curr in its place!
        a[k] := curr;
        n := n + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
