predicate P(x: int)

predicate Q(x: int)

method test()
    requires forall x {:trigger P(x)} :: P(x) && Q(x)
    ensures Q(0)
{
    // Since the precondition gives Q(x) for all x, in particular Q(0) holds
    assert Q(0);
}
function abs(a: real) : real {if a>0.0 then a else -a}
