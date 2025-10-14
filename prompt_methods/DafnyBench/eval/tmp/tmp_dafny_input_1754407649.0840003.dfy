
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
        invariant IsSorted(r)
        invariant |r| + |rest| == |s|
    {
        var x := rest[0];
        rest := rest[1..];
        var k := |r|;
        while k>0 && r[k-1]>x
            invariant 0 <= k <= |r|
            invariant forall i :: k <= i < |r| ==> r[i] > x
            invariant forall i :: 0 <= i < k ==> r[i] <= x
            invariant IsSorted(r)
        {
            k := k-1;
        }
        r := r[..k]+[x]+r[k..];
        assert IsSorted(r);
        assert multiset(r) + multiset(rest) == multiset(s);
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
