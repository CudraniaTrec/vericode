
// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
{
    // Setjið viðeigandi frumstillingar á m' og s hér.
    // m' er ný staðvær breyta en s er skilabreyta.
    s := [];
    var m' := m;

    while m' != multiset{}
        invariant multiset(s) + m' == m;
        invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
        invariant forall p | 0 <= p < |s| :: s[p] in m;
        invariant |s| + |m'| == |m|;
        decreases |m'|;
    {
        // Setjið viðeigandi stofn í lykkjuna hér
        var x := MinOfMultiset(m');
        assert x in m';
        assert forall y | y in m' :: x <= y;
        m' := m' - multiset{x};
        s := s + [x];
    }
    return s;
}

function abs(a: real) : real {if a>0.0 then a else -a}
