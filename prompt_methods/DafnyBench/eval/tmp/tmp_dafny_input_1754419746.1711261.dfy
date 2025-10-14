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
    m >= a && m >= b && (m == a || m == b)
}

// to check if it is functioning: postcondition not too accommodating
// the case it will refuse
lemma post_max_point_1(a:int, b:int, m:int)
    requires a > b
    requires m != a
    ensures !post_max(a, b, m)
{
    // If a > b, post_max(a, b, m) => m >= a && m >= b && (m == a || m == b)
    // If m != a, then (m == a || m == b) => m == b
    // But then m == b < a, so m >= a is false
    if m == b {
        assert m == b;
        assert b < a;
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
    // If m == b, then m >= a, but b < a, so contradiction
    if m == b {
        assert b < a;
        assert !(m >= a);
    }
    assert m == a;
}

lemma post_max_point_2(a:int, b:int, m:int)
    requires a == b
    requires m != a || m != b
    ensures !post_max(a, b, m)
{
    // If a == b, then m != a || m != b <=> m != a
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
    // If a < b, post_max(a, b, m) => m >= a && m >= b && (m == a || m == b)
    // If m != b, then (m == a || m == b) => m == a
    // But then m == a < b, so m >= b is false
    if m == a {
        assert a < b;
        assert !(m >= b);
    } else {
        assert !(m == a || m == b);
    }
}

lemma post_max_vertical_1(a:int, b:int, m:int)
    requires m != a && m != b
    ensures !post_max(a, b, m)
{
    assert !(m == a || m == b);
}

lemma post_max_vertical_1'(a:int, b:int, m:int)
    requires post_max(a, b, m)
    ensures m == a || m == b
{
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
        if a == b {
            // then m == m'
            assert m == m';
        } else if a > b {
            // m == a, m' == b, a > b, but m' >= a, so b >= a, contradiction
            assert m' >= a;
            assert false;
        } else {
            // a < b, m == a, m' == b, m >= b, so a >= b, contradiction
            assert m >= b;
            assert false;
        }
    } else if m == b && m' == a {
        if a == b {
            assert m == m';
        } else if b > a {
            assert m' >= b;
            assert false;
        } else {
            assert m >= a;
            assert false;
        }
    } else {
        assert m == m';
    }
}

lemma max_deterministic'(a:int, b:int, m:int, m':int)
    requires m != m'
    ensures !post_max(a, b, m) || !post_max(a, b, m')
{
    if post_max(a, b, m) && post_max(a, b, m') {
        assert m == m'; // by max_deterministic
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
