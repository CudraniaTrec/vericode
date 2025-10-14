
predicate IsDigit(c: char)
{
    48 <= c as int <= 57
}

method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
    ensures count >= 0
{
    count := 0;
    // Outer loop: i is the starting index of the substring
    var i: int := 0;
    while i <= |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant forall ii :: 0 <= ii < i ==>
            forall jj :: ii <= jj <= |s| ==>
                ( (jj == |s| || !IsDigit(s[jj])) && 
                  (sum := (if forall k :: ii <= k < jj ==> IsDigit(s[k]) then 
                              (sum2 := (sum3 := 0; var k := ii; while k < jj 
                                  invariant ii <= k <= jj
                                  invariant sum3 == sum2 + sum([s[x] as int - 48 | x := ii .. k]))
                              { sum3 := sum3 + (s[k] as int - 48); k := k + 1; } sum3)
                           else 0)) == jj - ii ==> true )
    {
        var sum := 0;
        var j: int := i;
        while j <= |s|
            invariant i <= j <= |s|
            invariant sum >= 0
            invariant sum <= if j == i then 0 else (j - i) * 9
            invariant forall k :: i <= k < j ==> IsDigit(s[k])
            decreases |s| - j
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
