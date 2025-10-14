method SwapFirstAndLast(a: array<int>)
    requires a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1])
    ensures a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{
    // Strongest possible: assert the elements before and after
    assert a.Length > 0;
    var old0 := a[0];
    var oldLast := a[a.Length - 1];
    // Assert that the middle elements are unchanged
    if a.Length > 2 {
        forall k | 1 <= k < a.Length - 1
            ensures a[k] == old(a[k])
        {
            // No-op, but for annotation
        }
    }
    var tmp := a[0];
    a[0] := a[a.Length - 1];
    a[a.Length - 1] := tmp;
    assert a[0] == oldLast;
    assert a[a.Length - 1] == old0;
    assert forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k]);
}
function abs(a: real) : real {if a>0.0 then a else -a}
