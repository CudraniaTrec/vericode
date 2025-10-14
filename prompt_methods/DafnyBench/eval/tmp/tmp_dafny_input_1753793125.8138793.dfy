predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    count := 0;
    var i := 1;
    // Only enter the loop if |s| >= 3, otherwise the range is empty
    while i < |s| - 1
        invariant 1 <= i <= |s|
        invariant count >= 0
        invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
        decreases |s| - 1 - i
    {
        // Only access s[i-1] and s[i+1] when 1 <= i < |s|-1
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
        }
        i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
