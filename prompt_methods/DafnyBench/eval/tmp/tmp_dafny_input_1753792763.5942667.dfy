predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
    ensures count >= 0
{
    count := 0;
    var i: int := 0;
    while i <= |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
    {
        var sum := 0;
        var j: int := i;
        while j <= |s|
            invariant i <= j <= |s|
            invariant sum >= 0
            invariant sum <= 9 * (j - i)
            invariant forall k :: i <= k < j ==> IsDigit(s[k])
        {
            if j == |s| || !IsDigit(s[j]) {
                if sum == j - i {
                    assert sum == j - i;
                    count := count + 1;
                }
                break;
            }
            sum := sum + (s[j] as int - 48);
            assert sum >= 0;
            if sum > j - i + 1 {
                break;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
