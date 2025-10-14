predicate P(x: int)

predicate Q(x: int)

method test()
    requires forall x {:trigger P(x)} :: P(x) && Q(x)
    ensures Q(0)
{
    // We do not know that Q(0) holds unless P(0) holds
    // So we assert P(0) first, then Q(0)
    assert P(0);
    assert Q(0);
}
function abs(a: real) : real {if a>0.0 then a else -a}
