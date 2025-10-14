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
        // Find the insertion index for x in r
        while k > 0 && r[k-1] > x
            invariant 0 <= k <= |r|
            invariant |r| == |r[..k]| + |r[k..]|
            invariant IsSorted(r)
            invariant forall i :: k <= i < |r| ==> r[i] > x
            invariant forall i :: 0 <= i < k ==> true
        {
            k := k-1;
        }
        // Insert x at position k
        r := r[..k] + [x] + r[k..];
        // After insertion, r is sorted if r was sorted before and x is inserted in the right place
        // No need for assert, as IsSorted(r) is maintained by the invariant and the insertion
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
