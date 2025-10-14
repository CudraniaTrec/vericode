predicate P(x: int)

predicate Q(x: int)

method test()
    requires forall x {:trigger P(x)} :: P(x) && Q(x)
    ensures Q(0)
{
    // Since the precondition states that for all x, Q(x) holds (because P(x) && Q(x), and P(x) can be arbitrary),
    // we can assert Q(0)
    assert P(0) && Q(0); // By instantiating the precondition with x = 0
    assert Q(0);
}
function abs(a: real) : real {if a>0.0 then a else -a}
