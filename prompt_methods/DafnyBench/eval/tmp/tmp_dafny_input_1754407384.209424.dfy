predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    count := 0;
    var n := |s|;
    if n < 3 {
        // No valid i in 1 <= i < n-1
        return;
    }
    var i := 1;
    while i < n-1
        invariant 1 <= i <= n-1
        invariant count >= 0
        invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
