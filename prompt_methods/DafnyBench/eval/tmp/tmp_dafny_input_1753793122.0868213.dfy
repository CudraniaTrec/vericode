predicate IsVowel(c: char)
{
    c in {'a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'}
}

method CountVowelNeighbors(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]) |
{
    var vowels := set i: int | 1 <= i < |s|-1 && IsVowel(s[i-1]) && IsVowel(s[i+1]);
    count := 0;
    var i := 1;
    while i < |s| - 1
        invariant 1 <= i <= |s|
        invariant count == | set j: int | 1 <= j < i && IsVowel(s[j-1]) && IsVowel(s[j+1]) |
        invariant forall j :: 1 <= j < i ==> (IsVowel(s[j-1]) && IsVowel(s[j+1]) ==> j in vowels)
        invariant forall j :: j in vowels && j < i ==> IsVowel(s[j-1]) && IsVowel(s[j+1])
        decreases |s| - i
    {
        if IsVowel(s[i-1]) && IsVowel(s[i+1]) {
            count := count + 1;
            assert i in vowels;
        }
        i := i + 1;
    }
    assert count == |vowels|;
}
function abs(a: real) : real {if a>0.0 then a else -a}
