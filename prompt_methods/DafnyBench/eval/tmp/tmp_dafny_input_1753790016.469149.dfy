method AssignmentsToMark(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{
    DivisionLemma(students, tutors);
    r := students / tutors;
    calc {
        // 1/tutors < 1 is not a valid Dafny expression, so we omit it.
        // Instead, we can assert the required property directly.
        assert students / tutors < students;
    }
}

lemma DivisionLemma(n:int, d:int)
    requires n > 0 && d > 1
    ensures n / d < n
{
    // Since d > 1, n/d <= n/2 < n for n > 0
    if n == 1 {
        assert n / d == 0 < 1 == n;
    } else {
        assert d > 1;
        assert n / d <= n / 2;
        assert n / 2 < n;
        assert n / d < n;
    }
}

method AssignmentsToMarkOne(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{
    r := students / tutors;
    calc {
        // 1/tutors < 1 is not a valid Dafny expression, so we omit it.
        // Instead, we can assert the required property directly.
        assert students / tutors < students;
    }
}

lemma CommonElement(a: array<nat>, b: array<nat>)
    requires a.Length > 0 && b.Length > 0 && a[0] == b[0]
    ensures multiset(a[..]) * multiset(b[..]) == multiset([a[0]]) + multiset(a[1..]) * multiset(b[1..])
{
    var E := multiset([a[0]]);
    assert multiset(a[..]) == E + multiset(a[1..]);
    assert multiset(b[..]) == E + multiset(b[1..]);
    calc {
        multiset(a[..]) * multiset(b[..]);
        (E + multiset(a[1..])) * (E + multiset(b[1..]));
        E + multiset(a[1..]) * multiset(b[1..]);
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
