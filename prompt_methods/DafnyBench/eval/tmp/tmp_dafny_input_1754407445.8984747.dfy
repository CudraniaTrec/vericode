
method CountEqualNumbers(a: int, b: int, c: int) returns (count: int)
    ensures count >= 0 && count <= 3
    ensures (count == 3) <==> (a == b && b == c)
    ensures (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c))
    ensures (count == 1) <==> (a != b && b != c && a != c)
{
    // Initially, assume all are different
    count := 1;
    assert count == 1;
    if (a == b) {
        count := count + 1;
        assert count == 2 || (a == b && b == c);
    }
    if (a == c) {
        count := count + 1;
        assert count == 2 || (a == b && b == c);
    }
    if (a != b && b == c) {
        count := count + 1;
        assert count == 2 || (a == b && b == c);
    }
    assert count >= 1 && count <= 3;
    assert (count == 3) <==> (a == b && b == c);
    assert (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c));
    assert (count == 1) <==> (a != b && b != c && a != c);
}

function abs(a: real) : real {if a>0.0 then a else -a}
