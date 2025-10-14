method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant mset == multiset(s[0..i])
    {
        mset := mset + multiset{s[i]};
        i := i + 1;
    }
    return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    // Compare the counts of all elements in s and t
    var allChars := {};
    // Collect all chars from s
    var scopy := s;
    while scopy != multiset{}
        invariant scopy + multiset(allChars) == s
        invariant allChars <= { x: char | s[x] > 0 }
        decreases |scopy|
    {
        var x :| x in scopy;
        allChars := allChars + {x};
        scopy := scopy - multiset{x};
    }
    // Collect all chars from t
    var tcopy := t;
    while tcopy != multiset{}
        invariant tcopy + multiset(allChars) == t + multiset(allChars - {x: char | t[x] > 0 && !(x in allChars)})
        invariant allChars <= { x: char | s[x] > 0 } + { x: char | t[x] > 0 }
        decreases |tcopy|
    {
        var x :| x in tcopy;
        allChars := allChars + {x};
        tcopy := tcopy - multiset{x};
    }
    // Now check counts for all chars in allChars
    var ok := true;
    var chars := allChars;
    while |chars| > 0
        invariant chars <= allChars
        invariant ok ==> forall x :: x in allChars - chars ==> s[x] == t[x]
        decreases |chars|
    {
        var x :| x in chars;
        if s[x] != t[x] {
            return false;
        }
        chars := chars - {x};
    }
    return true;
}

method isAnagram(s: string, t: string) returns (equal: bool)
    ensures (multiset(s) == multiset(t)) == equal
{
    var smset := toMultiset(s);
    var tmset := toMultiset(t);
    equal := msetEqual(smset, tmset);
}

function abs(a: real) : real {if a>0.0 then a else -a}
