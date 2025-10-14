method InsertSpacesBetweenCapitalWords(s: string) returns (res: string)
{
    var builder := "";
    if |s| == 0 {
        res := builder;
        return;
    }

    builder := builder + s[0..1];
    var i: int := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant |builder| == i
        decreases |s| - i
    {
        var c := s[i..i+1];
        var prev := s[i-1..i];
        // If current is uppercase and previous is not a space,
        // and previous is not uppercase
        if c[0] >= 'A' && c[0] <= 'Z' && prev[0] != ' ' {
            builder := builder + " ";
        }
        builder := builder + c;
        i := i + 1;
    }
    res := builder;
}