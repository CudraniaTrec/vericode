method ReverseWords(s: string) returns (res: string)
{
    // Split the string into words using spaces
    var words := new seq<string>;
    var curr := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant curr == "" ==> (i == 0 || s[i-1] == ' ')
        invariant curr != "" ==> s[i-|curr|..i] == curr
        invariant words + (if curr == "" then [] else [curr]) == WordsSoFar(s, i)
    {
        if s[i] == ' ' {
            if curr != "" {
                words := words + [curr];
                curr := "";
            }
        } else {
            curr := curr + s[i..i+1];
        }
        i := i + 1;
    }
    if curr != "" {
        words := words + [curr];
    }

    // Now reverse the sequence of words
    var revWords := words[..][::-1];

    // Join them with spaces
    res := if |revWords| == 0 then "" else revWords[0];
    i := 1;
    while i < |revWords|
        invariant 1 <= i <= |revWords|
        invariant res == JoinWithSpaces(revWords[..i])
    {
        res := res + " " + revWords[i];
        i := i + 1;
    }
}

// Helper function: computes the list of words parsed so far up to index i
function WordsSoFar(s: string, i: int): seq<string>
    decreases i
{
    if i == 0 then [] else
        if s[i-1] == ' ' then WordsSoFar(s, i-1)
        else
            var j := i-1;
            while j > 0 && s[j-1] != ' '
                decreases j
            {
                j := j - 1;
            }
            WordsSoFar(s, j) + [s[j..i]]
}

// Helper function: Joins a sequence of words with spaces
function JoinWithSpaces(words: seq<string>): string
{
    if |words| == 0 then "" else
        if |words| == 1 then words[0] else words[0] + " " + JoinWithSpaces(words[1..])
}