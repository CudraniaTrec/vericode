method Sort( m: multiset<int> ) returns ( s: seq<int> )
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
{
    s := [];
    var m' := m;

    while m' != multiset{}
        invariant multiset(s) + m' == m;
        invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
        invariant forall t | 0 <= t < |s| :: s[t] in m;
        invariant |s| + |m'| == |m|;
    {
        var x := 0;
        // Find the minimum element in m'
        x :| x in m' && forall z :: z in m' ==> x <= z;
        m' := m' - multiset{x};
        s := s + [x];
    }
    return s;
}

function abs(a: real) : real {if a>0.0 then a else -a}
