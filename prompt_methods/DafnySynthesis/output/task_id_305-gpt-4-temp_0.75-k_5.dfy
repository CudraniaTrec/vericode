// Dafny Code

method FindTwoPWords(words: seq<string>) returns (w1: string, w2: string)
    requires |words| >= 2
    ensures w1 in words && w2 in words && w1[0] == 'p' && w2[0] == 'p' && w1 != w2
{
    var found: seq<string> := [];
    // Collect words starting with 'p'
    for word in words {
        if |word| > 0 && word[0] == 'p' {
            found := found + [word];
            if |found| == 2 {
                break;
            }
        }
    }
    if |found| < 2 {
        // If fewer than 2 such words, return empty strings (or could also use {:unreachable})
        w1, w2 := "", "";
    } else {
        w1, w2 := found[0], found[1];
    }
}