
function maxcheck(s: array<nat>, i: int, max: int): int
requires 0 <= i <= s.Length
reads s
ensures forall x :: 0 <= x < i ==> maxcheck(s, i, max) >= s[x]
ensures maxcheck(s, i, max) >= max
ensures maxcheck(s, i, max) == if i == 0 then max else maxcheck(s, i - 1, if s[i - 1] > max then s[i - 1] else max)
{
    if i == 0 then max
    else if s[i - 1] > max then maxcheck(s, i - 1, s[i - 1])
    else maxcheck(s, i - 1, max)
}

method max(s: array<nat>) returns (a:int)
requires s.Length > 0
ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
ensures a in s[..]
{
    a := s[0];
    var i:int := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant a in s[..i]
        invariant forall x :: 0 <= x < i ==> a >= s[x]
    {
        if (s[i] > a) {
            a := s[i];
        }
        i := i + 1;
    }
    assert forall x :: 0 <= x < s.Length ==> a >= s[x];
    assert a in s[..];
}

method Checker() { 
    var a := new nat[][1,2,3,50,5,51]; 
    // ghost var  a := [1,2,3]; 
    var n := max(a); 
    // assert a[..] == [1,2,3]; 
    // assert MAXIMUM(1,2) == 2; 
    // assert ret_max(a,a.Length-1) == 12; 
    // assert ret_max(a,a.Length-1) == x+3; 
}

function abs(a: real) : real {if a>0.0 then a else -a}
