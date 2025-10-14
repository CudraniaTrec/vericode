
method is_anagram(s: string, t: string) returns (result: bool)
    requires |s| == |t|
    ensures (multiset(s) == multiset(t)) == result
{
    result := is_equal(multiset(s), multiset(t));
}


method is_equal(s: multiset<char>, t: multiset<char>) returns (result: bool)
    ensures (s == t) <==> result
{
    // Compare all possible characters
    var allChars := set c: char | s[c] > 0 || t[c] > 0;
    var equal := true;
    // Loop over all characters that appear in either multiset
    // (simulate a for loop using a set and a while loop)
    var charsChecked := set c: char | false;
    while charsChecked != allChars
        invariant charsChecked <= allChars
        invariant forall c: char :: c in charsChecked ==> s[c] == t[c]
        invariant equal ==> forall c: char :: c in charsChecked ==> s[c] == t[c]
        invariant !equal ==> exists c: char :: c in charsChecked && s[c] != t[c]
        decreases |allChars - charsChecked|
    {
        var c :| c in allChars - charsChecked;
        if s[c] != t[c] {
            equal := false;
            break;
        }
        charsChecked := charsChecked + {c};
    }
    result := equal;
}

function abs(a: real) : real {if a>0.0 then a else -a}
