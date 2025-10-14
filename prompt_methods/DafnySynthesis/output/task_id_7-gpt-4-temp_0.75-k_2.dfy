method FindAllLongWords(s: string) returns (words: seq<string>)
{
    // Split the string into words separated by whitespace
    var n := s.Length;
    var curr := 0;
    var wordList := new seq<string>[];
    while curr < n
        decreases n - curr
    {
        // Skip whitespace
        while curr < n && s[curr] <= ' '
            decreases n - curr
        {
            curr := curr + 1;
        }
        if curr >= n {
            break;
        }
        // Start of a word
        var start := curr;
        while curr < n && s[curr] > ' '
            decreases n - curr
        {
            curr := curr + 1;
        }
        var end_ := curr;
        var len := end_ - start;
        if len >= 4 {
            wordList := wordList + [s[start .. end_]];
        }
        // Loop continues
    }
    words := wordList;
}