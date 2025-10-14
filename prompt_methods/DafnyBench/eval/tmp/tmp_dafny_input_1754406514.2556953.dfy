method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{
    var v' : string := [];
    var k: int := 0;
    // v'[0..k) contains the result so far
    for i := 0 to |s1|
        invariant 0 <= i <= |s1|
        invariant 0 <= k <= i
        invariant |v'| == k
        invariant forall j :: 0 <= j < k ==> (v'[j] in s1) && !(v'[j] in s2)
        invariant forall j :: 0 <= j < i ==> (s1[j] in s2) || (exists l :: 0 <= l < k && v'[l] == s1[j])
    {
        if !(s1[i] in s2)
        {
            v' := v' + [s1[i]];
            k := k + 1;
            assert (v'[k-1] == s1[i]);
        }
    }
    v := v';
}
function abs(a: real) : real {if a>0.0 then a else -a}
