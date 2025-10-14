
method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{
    var n := 1;
    var tmp := a[0];
    // Invariant: For all 1 <= k < n, a[k] == old(a[k-1])
    //            a[0] == old(a[n-1])
    //            1 <= n <= a.Length
    //            For all n <= k < a.Length, a[k] == old(a[k])
    while n != a.Length
        invariant 1 <= n <= a.Length
        invariant a[0] == old(a[n-1])
        invariant forall k :: 1 <= k < n ==> a[k] == old(a[k-1])
        invariant forall k :: n <= k < a.Length ==> a[k] == old(a[k])
    {
        a[0], a[n] := a[n], a[0]; n := n + 1;
        assert a[0] == old(a[n-1]);
        assert forall k :: 1 <= k < n ==> a[k] == old(a[k-1]);
        assert forall k :: n <= k < a.Length ==> a[k] == old(a[k]);
    } 
}

function abs(a: real) : real {if a>0.0 then a else -a}
