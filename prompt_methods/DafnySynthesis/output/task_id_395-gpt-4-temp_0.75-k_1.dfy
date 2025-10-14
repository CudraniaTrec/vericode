method FirstNonRepeatedChar(s: string) returns (c: char)
    requires s != null
    ensures (exists i :: 0 <= i < |s| && (forall j :: 0 <= j < |s| && j != i ==> s[i] != s[j]) ==> c == s[(i:|0 <= i < |s| && (forall j :: 0 <= j < |s| && j != i ==> s[i] != s[j]))])
    ensures (forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |s| && j != i && s[i] == s[j]) ==> c == '\0'
{
    var freq := map[]; // map<char, int>
    // First pass: count frequency of each char
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall ch: char :: freq[ch] == (|set j: int | 0 <= j < i && s[j] == ch|)
    {
        var ch := s[i];
        if freq.Contains(ch) {
            freq := freq[ ch := freq[ch] + 1 ];
        } else {
            freq := freq[ ch := 1 ];
        }
        i := i + 1;
    }
    // Second pass: find first char with frequency 1
    i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k: int :: 0 <= k < i ==> freq[s[k]] != 1
    {
        if freq[s[i]] == 1 {
            c := s[i];
            return;
        }
        i := i + 1;
    }
    // If none found, return null char
    c := '\0';
}