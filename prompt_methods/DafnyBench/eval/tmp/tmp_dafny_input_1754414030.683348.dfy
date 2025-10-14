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
    // Compare the set of all elements in s and t
    var allElems := set x | x in s || x in t;
    var elemsChecked := set char{};
    while elemsChecked != allElems
        invariant elemsChecked <= allElems
        invariant forall x :: x in elemsChecked ==> s[x] == t[x]
    {
        var x :| x in allElems - elemsChecked;
        if s[x] != t[x] {
            return false;
        }
        elemsChecked := elemsChecked + {x};
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
