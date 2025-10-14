method ParabolaDirectrix(a: real, h: real, k: real) returns (directrix: real)
    requires a != 0.0
    ensures directrix == k - 1.0 / (4.0 * a)
{
    // a != 0.0 by precondition, so 4.0 * a != 0.0
    assert 4.0 * a != 0.0;
    // Division is safe
    directrix := k - 1.0 / (4.0 * a);
    assert directrix == k - 1.0 / (4.0 * a);
}
function abs(a: real) : real {if a>0.0 then a else -a}
