// method verifies
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
requires i >= 0 && j >= 0 && |s| >= 0;
requires |s| > 0 ==> i < |s| && j < |s|;
ensures multiset(s[..]) == multiset(t[..]);
ensures |s| == |t|;
ensures |s| > 0 ==> forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k]
ensures |s| > 0 ==> t[i] == s[j] && t[j] == s[i];
ensures |s| == 0 ==> t == s;
{
    t := s;
    if |s| == 0 {
        assert t == s;
        return t;
    }
    // At this point, |s| > 0, so i < |s| and j < |s| by precondition
    assert i < |s| && j < |s|;
    // Swap i and j
    var tmp := t[i];
    t := t[i := t[j]];
    t := t[j := tmp];

    // Postcondition assertions
    assert |t| == |s|;
    assert multiset(t[..]) == multiset(s[..]);
    assert t[i] == s[j] && t[j] == s[i];
    assert forall k:nat :: k != i && k != j && k < |s| ==> t[k] == s[k];
}

method check() {
    var a:string := "1scow2";
    var b:string := StringSwap(a, 1, 5);
    var c:string := "";
    var d:string := StringSwap(c, 1, 2);
}
// string == seq<Char>
//give se2011 ass2 ex1.dfy
function abs(a: real) : real {if a>0.0 then a else -a}
