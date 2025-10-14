
method toMultiset(s: string) returns (mset: multiset<char>)
    ensures multiset(s) == mset
{
    mset := multiset{};
    var i := 0;
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
    if |s| != |t| {
        return false;
    }
    ghost var checked: set<char> := {};
    var result := true;
    var sElems := s;
    while sElems != multiset{}
        invariant sElems + multiset(checked) == s
        invariant forall x :: x in checked ==> s[x] == t[x]
        decreases |sElems|
    {
        var x :| x in sElems;
        if s[x] != t[x] {
            return false;
        }
        checked := checked + {x};
        sElems := sElems - multiset[x := s[x]];
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
