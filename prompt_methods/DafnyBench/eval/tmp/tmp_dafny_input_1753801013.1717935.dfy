
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    var i: int;
    i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant mset == multiset(s[0..i])
    {
        // assert multiset(s) == multiset(s[0..i])+multiset{s[i]}+multiset(s[(i+1)..]);
        mset := mset + multiset{s[i]};
        i := i + 1;
    }
    // assert mset == multiset(s[0..|s|]);
    return mset;
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
    ensures s == t <==> equal
{
    ghost var sremoved: multiset<char> := multiset{};
    var scopy := s;
    while scopy != multiset{} 
        invariant sremoved + scopy == s
        invariant forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x]
        decreases |scopy|
    {
        var x :| x in scopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{};
        // assert removed[x := s[x]] <= s;
        sremoved := sremoved + removed[x := s[x]];
        scopy := scopy - removed[x := s[x]];
    }
    // assert scopy == multiset{};
    // assert s - sremoved == scopy;
    // assert sremoved == s;
    // assert forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x];

    ghost var tremoved: multiset<char> := multiset{};
    var tcopy := t;
    while tcopy != multiset{} 
        invariant tremoved + tcopy == t
        invariant forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x]
        decreases |tcopy|
    {
        var x :| x in tcopy;
        if !(x in t && s[x] == t[x]) {
           return false; 
        }
        var removed := multiset{};
        tremoved := tremoved + removed[x := s[x]];
        tcopy := tcopy - removed[x := s[x]];
    }
    // assert forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x];

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
