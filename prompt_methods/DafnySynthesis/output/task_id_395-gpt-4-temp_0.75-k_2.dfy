method FirstNonRepeatedChar(s: string) returns (c: char, found: bool)
{
    var counts := map[]; // map from char to int
    var n := s.Length;
    // First pass: count occurrences
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> s[j] in counts
        decreases n - i
    {
        var ch := s[i];
        if ch in counts {
            counts := counts[ ch := counts[ch] + 1 ];
        } else {
            counts := counts[ ch := 1 ];
        }
        i := i + 1;
    }

    // Second pass: find first with count 1
    i := 0;
    while i < n
        invariant 0 <= i <= n
        decreases n - i
    {
        var ch := s[i];
        if counts[ch] == 1 {
            c := ch;
            found := true;
            return;
        }
        i := i + 1;
    }
    found := false;
}