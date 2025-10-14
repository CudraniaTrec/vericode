method SwapFirstAndLast(a: array<int>)
    requires a != null && a.Length > 0
    modifies a
    ensures a[0] == old(a[a.Length - 1]) && a[a.Length - 1] == old(a[0])
    ensures forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k])
{
    // Strongest possible assertions before and after each step
    assert a != null && a.Length > 0;
    assert forall k :: 0 <= k < a.Length ==> a[k] == old(a[k]);
    var temp := a[0];
    assert temp == old(a[0]);
    a[0] := a[a.Length - 1];
    assert a[0] == old(a[a.Length - 1]);
    assert a[a.Length - 1] == old(a[a.Length - 1]);
    assert forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k]);
    a[a.Length - 1] := temp;
    assert a[0] == old(a[a.Length - 1]);
    assert a[a.Length - 1] == old(a[0]);
    assert forall k :: 1 <= k < a.Length - 1 ==> a[k] == old(a[k]);
}
function abs(a: real) : real {if a>0.0 then a else -a}
