
method AbsIt(s: array<int>) modifies s;
//requires 
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
ensures forall x :: 0 <= x < s.Length ==> old(s[x]) >= 0 ==> s[x] == old(s[x])

{
    var i:int := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall x :: 0 <= x < i ==> s[x] >= 0
        invariant forall x :: 0 <= x < i ==> old(s[x]) < 0 ==> s[x] == -old(s[x])
        invariant forall x :: 0 <= x < i ==> old(s[x]) >= 0 ==> s[x] == old(s[x])
        invariant forall x :: i <= x < s.Length ==> s[x] == old(s[x])
    {
        if (s[i] < 0) {
            s[i] := -s[i];
            assert s[i] == -old(s[i]);
        } else {
            assert s[i] == old(s[i]);
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
