method ReverseWords(s: string) returns (res: string)
{
    var n := s.Length;
    var words: seq<string> := [];
    var currentWord := "";
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant currentWord != null
        invariant words != null
    {
        if s[i] == ' ' {
            if |currentWord| > 0 {
                words := words + [currentWord];
                currentWord := "";
            }
        } else {
            currentWord := currentWord + s[i..i+1];
        }
        i := i + 1;
    }
    if |currentWord| > 0 {
        words := words + [currentWord];
    }
    // Now reverse the sequence of words
    var revWords := words[::][^-1]; // reverse the sequence
    // Join the words with single space
    if |revWords| == 0 {
        res := "";
    } else {
        res := revWords[0];
        var j := 1;
        while j < |revWords|
            invariant 1 <= j <= |revWords|
            invariant res != null
        {
            res := res + " " + revWords[j];
            j := j + 1;
        }
    }
}