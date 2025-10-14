
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
        var y: int;
        y :| y in m' && forall z :: z in m' ==> y <= z;
        m' := m' - multiset{y};
        s := s + [y];
    }
    return s;
}

function abs(a: real) : real {if a>0.0 then a else -a}
