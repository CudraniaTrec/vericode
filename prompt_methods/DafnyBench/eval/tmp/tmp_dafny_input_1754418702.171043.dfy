
// verifies
// check that string between indexes low and high-1 are sorted
predicate Sorted(a: string, low:int, high:int)
requires 0 <= low <= high <= |a|
{ 
    forall j, k :: low <= j < k < high ==> a[j] <= a[k] 
}

method String3Sort(a: string) returns (b: string) 
requires |a| == 3;
ensures Sorted(b, 0, |b|);
ensures |a| == |b|;
ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
{
    b := a;
    // Invariant: multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]}
    // Invariant: |b| == 3
    // Invariant: 0 <= 0 <= 3 <= |b|
    assert |b| == 3;
    assert multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
    if (b[0] > b[1]) {
        b := b[0 := b[1]][1 := b[0]];
        assert multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
    }
    if (b[1] > b[2]) {
        b := b[1 := b[2]][2 := b[1]];
        assert multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
    }
    if (b[0] > b[1]) {
        b := b[0 := b[1]][1 := b[0]];
        assert multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
    }
    assert Sorted(b, 0, |b|);
    assert |b| == 3;
    assert multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]};
}

method check() {
    var a:string := "cba";
    var b:string := String3Sort(a);

    var a1:string := "aaa";
    var b1:string := String3Sort(a1);

    var a2:string := "abc";
    var b2:string := String3Sort(a2);

    var a3:string := "cab";
    var b3:string := String3Sort(a3);

    var a4:string := "bac";
    var b4:string := String3Sort(a4);

    var a5:string := "bba";
    var b5:string := String3Sort(a5);

    var a6:string := "aba";
    var b6:string := String3Sort(a6);

    var a7:string := "acb";
    var b7:string := String3Sort(a7);

    var a8:string := "bca";
    var b8:string := String3Sort(a8);

    var a9:string := "bab";
    var b9:string := String3Sort(a9);

    var a10:string := "abb";
    var b10:string := String3Sort(a10);
}

function abs(a: real) : real {if a>0.0 then a else -a}
