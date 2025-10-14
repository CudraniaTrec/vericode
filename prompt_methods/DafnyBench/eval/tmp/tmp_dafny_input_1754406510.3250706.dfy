
method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{
    var v' : string := [];
    // Invariant: v' contains exactly those s1[j] for 0 <= j < i where s1[j] !in s2
    // Invariant: |v'| <= i
    // Invariant: forall j :: 0 <= j < |v'| ==> (v'[j] in s1) && !(v'[j] in s2)
    // Invariant: forall j :: 0 <= j < i ==> (s1[j] in s2) || (s1[j] in v')
    // Invariant: forall j :: 0 <= j < |s1| ==> j < i || ((s1[j] in s2) || (s1[j] !in v'))
    for i := 0 to |s1|
        invariant 0 <= i <= |s1|
        invariant |v'| <= i
        invariant forall j :: 0 <= j < |v'| ==> (v'[j] in s1) && !(v'[j] in s2)
        invariant forall j :: 0 <= j < i ==> (s1[j] in s2) || (s1[j] in v')
        invariant forall j :: 0 <= j < |s1| ==> j < i || ((s1[j] in s2) || (s1[j] !in v'))
    {
        if !(s1[i] in s2)
        {
            v' := v' + [s1[i]];
            assert (s1[i] in s1) && !(s1[i] in s2);
        }
    }
    v := v';
}

function abs(a: real) : real {if a>0.0 then a else -a}
