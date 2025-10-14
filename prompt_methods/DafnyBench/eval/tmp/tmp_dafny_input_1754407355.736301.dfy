predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}


method CountDigits(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
    var digits := set i: int | 0 <= i < |s| && IsDigit(s[i]);
    assert forall i :: 0 <= i < |s| && IsDigit(s[i]) ==> i in digits;
    assert forall i :: i in digits ==> 0 <= i < |s| && IsDigit(s[i]);
    count := |digits|;
    assert count >= 0;
    assert count == | set i: int | 0 <= i < |s| && IsDigit(s[i])|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
