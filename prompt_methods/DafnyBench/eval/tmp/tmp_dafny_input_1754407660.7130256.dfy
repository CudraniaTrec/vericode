// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{
    r := [];
    var rest := s;
    while rest != []
        invariant multiset(r) + multiset(rest) == multiset(s)
        invariant |r| + |rest| == |s|
        invariant IsSorted(r)
    {
        var x := rest[0];
        rest := rest[1..];
        var k := |r|;
        while k > 0 && r[k-1] > x
            invariant 0 <= k <= |r|
            invariant |r| == |r[..k]| + |r[k..]|
            invariant IsSorted(r)
            invariant forall i :: k <= i < |r| ==> r[i] > x
        {
            k := k-1;
        }
        r := r[..k] + [x] + r[k..];
        // IsSorted(r) is preserved by construction
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
