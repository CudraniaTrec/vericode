
// problem 3:
// name:      ....... (fill in your name)
// s-number: s....... (fill in your student number)
// table:     ....... (fill in your table number)

method problem3(m:int, X:int) returns (r:int)
requires X >= 0 && (2*m == 1 - X || m == X + 3)
ensures r == X
{
    r := m;
    assert r == m;
    if (1-2*r >= 0) {
        // Case 1: 1 - 2*r >= 0  ==> 2*r <= 1
        // From precondition: 2*m == 1 - X
        assert 2*m == 1 - X || m == X + 3;
        assert r == m;
        r := 2*r;
        assert r == 2*m;
        r := -r+1;
        assert r == -2*m + 1;
        // Now, from precondition: 2*m == 1 - X
        // So, 2*m = 1 - X  ==> 2*m + X = 1  ==> X = 1 - 2*m
        // So, r = -2*m + 1 = X
        assert 2*m == 1 - X;
        assert r == X;
    } else {
        // Case 2: 1 - 2*r < 0  ==> 2*r > 1
        // From precondition: m == X + 3
        assert 2*m == 1 - X || m == X + 3;
        assert r == m;
        r := r -3;
        assert r == m - 3;
        // m == X + 3  ==> m - 3 == X
        assert m == X + 3;
        assert r == X;
    }
    assert r == X;
}

function abs(a: real) : real {if a>0.0 then a else -a}
