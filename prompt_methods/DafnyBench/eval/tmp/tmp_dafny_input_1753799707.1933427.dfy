
method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
    var i := 0;
    while i < a.Length && i < b.Length 
        invariant 0 <= i <= a.Length && 0 <= i <= b.Length
        invariant forall j :: 0 <= j < i ==> a[j] == b[j]
        invariant 
            (forall j :: 0 <= j < i ==> a[j] == b[j]) ==>
                (forall k :: 0 <= k < i ==> a[..k] == b[..k])
        invariant 
            (exists k :: 0 <= k < i && a[k] < b[k]) ==> 
                (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
        invariant 
            (forall j :: 0 <= j < i ==> a[j] == b[j]) ==>
                (a[..i] == b[..i])
    {
        if a[i] < b[i] { 
            assert a[..i] == b[..i];
            assert 0 <= i < a.Length && i < b.Length;
            assert a[..i] == b[..i] && a[i] < b[i];
            return true; 
        }
        else if a[i] > b[i] { 
            assert a[..i] == b[..i];
            assert 0 <= i < a.Length && i < b.Length;
            assert a[i] > b[i];
            return false; 
        }
        else {
            assert a[i] == b[i];
            i := i + 1; 
        }
    }
    assert i == a.Length || i == b.Length;
    assert a[..i] == b[..i];
    return a.Length <= b.Length;
}

method testLeq() {
    var b := new int[][1, 2];
    var a1 := new int[][]; var r1 := leq(a1, b); assert r1;
    var a2 := new int[][1]; var r2 := leq(a2, b); assert r2;
    var a3 := new int[][1, 2]; var r3 := leq(a3, b); assert r3;
    var a4 := new int[][1, 1, 2]; var r4 := leq(a4, b); assert a4[1]<b[1] && r4;
    var a5 := new int[][1, 2, 3]; var r5 := leq(a5, b); assert !r5;
    var a6 := new int[][2]; var r6 := leq(a6, b); assert !r6;
}

function abs(a: real) : real {if a>0.0 then a else -a}
