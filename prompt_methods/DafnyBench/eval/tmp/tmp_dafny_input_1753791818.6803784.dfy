method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{
    var v' : string := [];
    var i: int := 0;
    while i < |s1|
        invariant 0 <= i <= |s1|
        invariant |v'| <= i
        invariant forall j :: 0 <= j < |v'| ==> (v'[j] in s1[0..i]) && !(v'[j] in s2)
        invariant forall j :: 0 <= j < i ==> (s1[j] in s2) || (s1[j] in v')
    {
        if !(s1[i] in s2)
        {
            v' := v' + [s1[i]];
            // v'[|v'|-1] == s1[i], and s1[i] not in s2
            assert v'[|v'|-1] == s1[i];
            assert !(s1[i] in s2);
        }
        i := i + 1;
    }
    v := v';
    assert |v| <= |s1|;
    assert forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2);
    assert forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v);
    return v;
}

function abs(a: real) : real {if a>0.0 then a else -a}
