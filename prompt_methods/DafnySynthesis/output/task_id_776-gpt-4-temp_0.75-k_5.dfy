// Dafny Code

method CountCharsWithVowelNeighbors(s: string) returns (count: int)
    ensures 0 <= count <= |s|
{
    count := 0;
    var n := |s|;

    // Helper function to determine if a character is a vowel (case insensitive)
    function method IsVowel(c: char): bool
    {
        c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
        c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
    }

    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= count <= i
    {
        var hasVowelNeighbor := false;
        if i > 0 && IsVowel(s[i - 1]) {
            hasVowelNeighbor := true;
        }
        if i < n - 1 && IsVowel(s[i + 1]) {
            hasVowelNeighbor := true;
        }
        if hasVowelNeighbor {
            count := count + 1;
        }
        i := i + 1;
    }
}