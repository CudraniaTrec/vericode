
// Dafny is designed to be familiar to those programming in an OOP language like
// Java, so, we have plain old ordinary mutable arrays rather than the functional
// list data structures that we saw in Coq.  This means that unlike our Coq
// and Python examples, we can sort our array in-place and avoid needing a whole
// bunch of intermediary allocations.

// Just as before, we need a way of defining what it means for an array of nats
// to be sorted:
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
        invariant multiset(a[..n]) + multiset(a[n..]) == multiset(a[..])
    {

        var curr := a[n];

        // 1. Find our pivot position k, the location where we should insert the
        // current value.
        var k := n;
        while k > 0 && a[k-1] > curr
            invariant 0 <= k <= n
            invariant forall i :: 0 <= i < k ==> a[i] <= curr
            invariant forall i :: k <= i < n ==> a[i] > curr
            invariant sorted(a[..n])
            invariant multiset(a[..n]) + multiset(a[n..]) == multiset(a[..])
        {
            k := k-1;
        }

        // 2. Shift all elements between k and n to the right by one.
        var j := n-1;
        while j >= k
            invariant k-1 <= j < n
            invariant forall p :: j+1 <= p <= n ==> a[p] == a[p-1]
            invariant forall p :: 0 <= p < k ==> a[p] <= curr
            invariant forall p :: k <= p <= j ==> a[p] > curr
            invariant sorted(a[..n])
            invariant multiset(a[..n]) + multiset(a[n..]) == multiset(a[..])
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
