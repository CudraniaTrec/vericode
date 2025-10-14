
// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/GW7a

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://www.rise4fun.com/Dafny/JPGct

// Klárið að forrita föllin tvö.

method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
    ensures forall z | z in pre :: z <= p;
    ensures forall z | z in post :: z >= p;
{
    p :| p in m;
    var m' := m;
    m' := m' - multiset{p};
    pre := multiset{};
    post := multiset{};
    while m' != multiset{}
        invariant m == pre + multiset{p} + post + m'
        invariant pre <= m
        invariant post <= m
        invariant p in m
        invariant multiset{p} <= m
        invariant forall z | z in pre :: z <= p
        invariant forall z | z in post :: z >= p
        invariant pre * post == multiset{} // pre and post are disjoint
        decreases |m'|
    {
        var temp :| temp in m';
        m' := m' - multiset{temp};
        if temp <= p
        {
            pre := pre + multiset{temp};
            assert temp <= p;
        }
        else
        {
            post := post + multiset{temp};
            assert temp > p;
        }
    }
    assert m == pre + multiset{p} + post;
    assert forall z | z in pre :: z <= p;
    assert forall z | z in post :: z >= p;
    return pre,p,post;
        
}

    





method QuickSelect( m: multiset<int>, k: int )
        returns( pre: multiset<int>, kth: int, post: multiset<int> )
    requires 0 <= k < |m|;
    ensures kth in m;
    ensures m == pre+multiset{kth}+post;
    ensures |pre| == k;
    ensures forall z | z in pre :: z <= kth;
    ensures forall z | z in post :: z >= kth;
{
    pre,kth,post := Partition(m);
    assert kth in m;
    assert m == pre + multiset{kth} + post;
    assert forall z | z in pre :: z <= kth;
    assert forall z | z in post :: z >= kth;
    if |pre| != k
    {
        if k > |pre|
        {
            assert k - |pre| - 1 >= 0;
            assert k - |pre| - 1 < |post|;
            var pre',p,post' := QuickSelect(post,k-|pre| - 1);
            assert p in post;
            assert post == pre' + multiset{p} + post';
            pre := pre + multiset{kth} + pre';
            post := post - pre' - multiset{p};
            kth := p;
            assert kth in m;
            assert m == pre + multiset{kth} + post;
            assert |pre| == k;
            assert forall z | z in pre :: z <= kth;
            assert forall z | z in post :: z >= kth;
        }
        else if k < |pre|
        {
            assert k >= 0;
            assert k < |pre|;
            var pre',p,post' := QuickSelect(pre,k);
            assert p in pre;
            assert pre == pre' + multiset{p} + post';
            pre := pre - multiset{p} - post';
            post := post + multiset{kth} + post';
            kth := p;
            assert kth in m;
            assert m == pre + multiset{kth} + post;
            assert |pre| == k;
            assert forall z | z in pre :: z <= kth;
            assert forall z | z in post :: z >= kth;
        }
    }
    else{
        assert kth in m;
        assert m == pre + multiset{kth} + post;
        assert |pre| == k;
        assert forall z | z in pre :: z <= kth;
        assert forall z | z in post :: z >= kth;
        return pre,kth,post;
    } 
}

function abs(a: real) : real {if a>0.0 then a else -a}
