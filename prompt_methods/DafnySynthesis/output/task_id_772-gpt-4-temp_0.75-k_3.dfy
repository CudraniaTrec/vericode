method RemoveWordsWithKLength(s: string, k: nat) returns (res: string)
{
    var i := 0;
    res := "";
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res != null
    {
        // Skip leading spaces
        while i < |s| && s[i] == ' '
            invariant 0 <= i <= |s|
        {
            res := res + s[i..i+1];
            i := i + 1;
        }
        if i >= |s| {
            break;
        }
        // Find word start
        var start := i;
        while i < |s| && s[i] != ' '
            invariant start <= i <= |s|
        {
            i := i + 1;
        }
        var word := s[start..i];
        if |word| != k {
            res := res + word;
        }
    }
    // Remove any trailing spaces (optional)
    // Uncomment if trailing spaces should be trimmed
    // while |res| > 0 && res[|res|-1] == ' ' 
    // {
    //     res := res[..|res|-1];
    // }
}