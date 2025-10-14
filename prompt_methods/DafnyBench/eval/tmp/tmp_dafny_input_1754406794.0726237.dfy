predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
    var uppercase := set i: int | 0 <= i < |s| && IsUpperCase(s[i]);
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == |set j: int | 0 <= j < i && IsUpperCase(s[j])|
        invariant forall j :: 0 <= j < i ==> (IsUpperCase(s[j]) ==> j in uppercase)
        invariant uppercase == set k: int | 0 <= k < |s| && IsUpperCase(s[k])
    {
        if IsUpperCase(s[i]) {
            count := count + 1;
            assert i in uppercase;
        }
        i := i + 1;
    }
    assert count == |uppercase|;
}
function abs(a: real) : real {if a>0.0 then a else -a}
