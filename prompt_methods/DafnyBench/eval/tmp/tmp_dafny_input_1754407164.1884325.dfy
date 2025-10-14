
predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
    ensures count >= 0
{
    count := 0;
    // Outer loop: i is the start index of the substring
    var i: int := 0;
    while i <= |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant forall k: int :: 0 <= k < i ==> 
            forall l: int :: k <= l <= |s| ==>
                ( (l == |s| || !IsDigit(s[l-1])) && 
                  (var sum := sumDigits(s, k, l-1); sum == l-k ==> old(count) + 1 <= count) )
    {
        var sum := 0;
        var j: int := i;
        while j <= |s|
            invariant i <= j <= |s|
            invariant sum >= 0
            invariant forall k: int :: i <= k < j ==> IsDigit(s[k])
            invariant sum == sumDigits(s, i, j-1)
        {
            if j == |s| || !IsDigit(s[j]) {
                if sum == j - i {
                    count := count + 1;
                    assert count >= 0;
                }
                break;
            }
            sum := sum + (s[j] as int - 48);
            assert sum == sumDigits(s, i, j);
            if sum > j - i + 1 {
                break;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

// Helper function to compute sum of digits in s from index lo to hi (inclusive)
function sumDigits(s: string, lo: int, hi: int): int
    requires 0 <= lo <= hi+1 <= |s|
    requires forall k: int :: lo <= k <= hi ==> IsDigit(s[k])
{
    if lo > hi then 0 else (s[lo] as int - 48) + sumDigits(s, lo+1, hi)
}

function abs(a: real) : real {if a>0.0 then a else -a}
