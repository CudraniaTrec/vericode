method RemoveFirstAndLastOccurrence(s: string, c: char) returns (res: string)
{
    var first := -1;
    var last := -1;

    // Find first and last occurrence of c
    var i := 0;
    while i < |s|
        decreases |s| - i
    {
        if s[i] == c {
            if first == -1 {
                first := i;
            }
            last := i;
        }
        i := i + 1;
    }

    if first == -1 || first == last {
        // c not found, or only one occurrence
        res := s;
        return;
    }

    // Build new string without first and last occurrence
    var builder := "";
    i := 0;
    while i < |s|
        decreases |s| - i
    {
        if i != first && i != last {
            builder := builder + s[i .. i+1];
        }
        i := i + 1;
    }
    res := builder;
}