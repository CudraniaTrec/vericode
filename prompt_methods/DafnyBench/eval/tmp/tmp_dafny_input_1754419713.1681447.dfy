
lemma max(a:int, b:int) returns (m:int)
    ensures m >= a
    ensures m >= b
    ensures m == a || m == b
{
    if (a > b) {
        m := a;
        assert m >= a;
        assert m >= b;
        assert m == a || m == b;
    } else {
        m := b;
        assert m >= a;
        assert m >= b;
        assert m == a || m == b;
    }
}

predicate post_max(a:int, b:int, m:int)
{
    && m >= a
    && m >= b
    && (m == a || m == b)
}

// to check if it is functioning: postcondition not too accommodating
// the case it will refuse
lemma post_max_point_1(a:int, b:int, m:int)
    requires a > b
    requires m != a
    ensures !post_max(a, b, m)
{
    // If m != a, but a > b, then m must be b or something else.
    // But m >= a, m >= b, and (m == a || m == b) must all hold for post_max.
    // Since m != a, the only way is m == b, but then a > b, so m == b < a, so m >= a fails.
    assert m != a;
    assert a > b;
    if m == b {
        assert m < a;
        assert !(m >= a);
    } else {
        assert !(m == a || m == b);
    }
}

lemma post_max_point_1'(a:int, b:int, m:int)
    requires a > b
    requires post_max(a, b, m)
    ensures m == a
{
    // post_max(a, b, m) => m >= a && m >= b && (m == a || m == b)
    // If a > b, and m == a or m == b, but if m == b, then m < a, so m >= a fails.
    if m == b {
        assert m < a;
        assert !(m >= a);
        assert !post_max(a, b, m);
    }
    assert m == a;
}

lemma post_max_point_2(a:int, b:int, m:int)
    requires a == b
    requires m != a || m != b
    ensures !post_max(a, b, m)
{
    // If a == b, then m != a || m != b means m != a (since m == a iff m == b)
    // So m != a, so m != a && m != b, so (m == a || m == b) is false
    assert a == b;
    assert m != a;
    assert m != b;
    assert !(m == a || m == b);
}

lemma post_max_point_3(a:int, b:int, m:int)
    requires a < b
    requires m != b
    ensures !post_max(a, b, m)
{
    // If a < b, and m != b, then m == a or something else.
    // If m == a, then m >= b? But a < b, so m == a < b, so m >= b fails.
    if m == a {
        assert m < b;
        assert !(m >= b);
    } else {
        assert !(m == a || m == b);
    }
}

lemma post_max_vertical_1(a:int, b:int, m:int)
    requires m != a && m != b
    ensures !post_max(a, b, m)
{
    // (m == a || m == b) is false
    assert !(m == a || m == b);
}

lemma post_max_vertical_1'(a:int, b:int, m:int)
    requires post_max(a, b, m)
    ensures m == a || m == b
{
    assert post_max(a, b, m);
    assert m == a || m == b;
}

// to check if it is implementable
lemma post_max_realistic_1(a:int, b:int, m:int)
    requires a > b
    requires m == a
    ensures post_max(a, b, m)
{
    assert m == a;
    assert m >= a;
    assert m >= b;
    assert m == a || m == b;
}

lemma post_max_realistic_2(a:int, b:int, m:int)
    requires a < b
    requires m == b
    ensures post_max(a, b, m)
{
    assert m == b;
    assert m >= a;
    assert m >= b;
    assert m == a || m == b;
}

lemma post_max_realistic_3(a:int, b:int, m:int)
    requires a == b
    requires m == a
    ensures post_max(a, b, m)
{
    assert m == a;
    assert m == b;
    assert m >= a;
    assert m >= b;
    assert m == a || m == b;
}


// this form is more natural
lemma max_deterministic(a:int, b:int, m:int, m':int)
    // should include preconditions if applicable
    requires post_max(a, b, m)
    requires post_max(a, b, m')
    ensures m == m'
{
    // Both m and m' are a or b, and both >= a and >= b
    if m == a && m' == b {
        assert m == a && m' == b;
        // m >= b, m' >= a
        if a > b {
            assert m == a && a > b;
            assert m >= b;
            assert m' == b;
            assert m' >= a;
            assert false; // b >= a is false if a > b
        } else if a < b {
            assert m == a && a < b;
            assert m >= b;
            assert false; // a < b, so a >= b is false
        } else {
            assert a == b;
            assert m == a && m' == b && a == b;
            assert m == m';
        }
    }
    if m == b && m' == a {
        // symmetric case
        if b > a {
            assert false;
        } else if b < a {
            assert false;
        } else {
            assert m == m';
        }
    }
    assert m == m';
}

lemma max_deterministic'(a:int, b:int, m:int, m':int)
    requires m != m'
    ensures !post_max(a, b, m) || !post_max(a, b, m')
{
    if post_max(a, b, m) && post_max(a, b, m') {
        assert m == m'; // by max_deterministic
        assert false;
    }
}

lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper<T>(
        s: seq<int>,
        b: int,
        i: nat
    )
    requires |s| > i 
    requires b == s[i]
    ensures s[..i] + [b] == s[..i+1]
{
    // s[..i+1] == s[..i] + [s[i]]
    assert s[..i+1] == s[..i] + [s[i]];
    assert b == s[i];
    assert s[..i] + [b] == s[..i] + [s[i]];
    assert s[..i] + [b] == s[..i+1];
}

lemma multisetEquality(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
   requires m1 > m2 + m3
   requires m1 == m2 + m4
   ensures m3 < m4
{
    // m1 > m2 + m3 means m1 >= m2 + m3 and m1 != m2 + m3
    // m1 == m2 + m4, so m2 + m4 >= m2 + m3 and m2 + m4 != m2 + m3
    // So m4 >= m3 and m4 != m3, so m3 < m4
    assert m1 >= m2 + m3;
    assert m1 != m2 + m3;
    assert m1 == m2 + m4;
    assert m2 + m4 >= m2 + m3;
    assert m4 >= m3;
    assert m4 != m3;
    assert m3 < m4;
}

function abs(a: real) : real {if a>0.0 then a else -a}
