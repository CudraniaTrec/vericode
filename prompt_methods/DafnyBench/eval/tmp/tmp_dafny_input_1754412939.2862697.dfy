
// problem 3:
// name:      ....... (fill in your name)
// s-number: s....... (fill in your student number)
// table:     ....... (fill in your table number)

method problem3(m:int, X:int) returns (r:int)
requires X >= 0 && (2*m == 1 - X || m == X + 3)
ensures r == X
{
    r := m;
    // At this point:
    // assert r == m;
    // assert X >= 0 && (2*r == 1 - X || r == X + 3);

    if (1-2*r >= 0) {
        // assert 2*r == 1 - X; // Since 1-2*r >= 0, must have 2*r == 1-X by precondition
        r := 2*r;
        // assert r == 2*m && r == 1-X;
        r := -r+1;
        // assert r == - (1-X) + 1;
        // assert r == X;
    } else {
        // assert r == X + 3; // Since 1-2*r < 0, must have m == X+3 by precondition, so r == X+3
        r := r -3;
        // assert r == X+3-3;
        // assert r == X;
    }
    // assert r == X;
}

function abs(a: real) : real {if a>0.0 then a else -a}
