method Sort( m: multiset<int> ) returns ( s: seq<int> )
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
{
    s := [];
    var m' := m;

    while m' != multiset{}
        invariant multiset(s) + m' == m;
        invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
        invariant forall p | 0 <= p < |s| :: s[p] in m;
        invariant |s| + |m'| == |m|;
        invariant forall y | y in m' :: (|s| == 0) || s[|s|-1] <= y;
        decreases |m'|;
    {
        var x :| x in m' && forall y | y in m' :: x <= y;
        m' := m' - multiset{x};
        s := s + [x];
    }
    return s;
}

function abs(a: real) : real {if a>0.0 then a else -a}
