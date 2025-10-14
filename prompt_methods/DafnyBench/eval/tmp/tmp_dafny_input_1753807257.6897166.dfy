
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
    // m != a, so if post_max(a, b, m) held, we'd need m == b and m >= a, but a > b, so b < a, so m < a, contradiction.
    assert m != a;
    assert a > b;
    if m == b {
        assert m < a;
        assert !(m >= a);
    }
    assert !post_max(a, b, m);
}

// an equivalent way of doing so
lemma post_max_point_1'(a:int, b:int, m:int)
    requires a > b
    requires post_max(a, b, m)
    ensures m == a
{
    // post_max(a, b, m) gives m >= a, m >= b, m == a || m == b
    // If m == b, then m >= a, but b < a, so b >= a is false
    if m == b {
        assert b < a;
        assert !(b >= a);
        assert false;
    }
    assert m == a;
}

lemma post_max_point_2(a:int, b:int, m:int)
    requires a == b
    requires m != a || m != b
    ensures !post_max(a, b, m)
{
    // m != a || m != b, but a == b, so m != a || m != a, so m != a
    assert a == b;
    assert m != a;
    // So m == a || m == b is false
    assert !(m == a || m == b);
    assert !post_max(a, b, m);
}

lemma post_max_point_3(a:int, b:int, m:int)
    requires a < b
    requires m != b
    ensures !post_max(a, b, m)
{
    // m != b, so if post_max(a, b, m) held, m == a, but a < b, so m < b, so m >= b is false
    assert a < b;
    assert m != b;
    if m == a {
        assert m < b;
        assert !(m >= b);
    }
    assert !post_max(a, b, m);
}

lemma post_max_vertical_1(a:int, b:int, m:int)
    requires m != a && m != b
    ensures !post_max(a, b, m)
{
    // m != a && m != b, so m == a || m == b is false
    assert !(m == a || m == b);
    assert !post_max(a, b, m);
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
    assert m >= b; // since a > b, m == a > b
    assert m == a || m == b;
}

lemma post_max_realistic_2(a:int, b:int, m:int)
    requires a < b
    requires m == b
    ensures post_max(a, b, m)
{
    assert m == b;
    assert m >= a; // since b > a
    assert m >= b;
    assert m == a || m == b;
}

lemma post_max_realistic_3(a:int, b:int, m:int)
    requires a == b
    requires m == a
    ensures post_max(a, b, m)
{
    assert a == b;
    assert m == a;
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
    // Both m and m' are equal to a or b
    if m == a {
        if m' == a {
            assert m == m';
        } else {
            assert m' == b;
            // post_max(a, b, m): m == a, m >= b
            // post_max(a, b, m'): m' == b, m' >= a
            // So a == b
            assert a == b;
            assert m == m';
        }
    } else {
        assert m == b;
        if m' == b {
            assert m == m';
        } else {
            assert m' == a;
            assert a == b;
            assert m == m';
        }
    }
}

lemma max_deterministic'(a:int, b:int, m:int, m':int)
    requires m != m'
    ensures !post_max(a, b, m) || !post_max(a, b, m')
{
    // If both post_max(a, b, m) and post_max(a, b, m') hold, then m == m' by max_deterministic
    // Contrapositive: if m != m', then at least one does not hold
    if post_max(a, b, m) && post_max(a, b, m') {
        assert m == m'; // by max_deterministic
        assert false;
    }
    assert !post_max(a, b, m) || !post_max(a, b, m');
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
    assert s[..i] + [b] == s[..i] + [s[i]];
    assert s[..i+1] == s[..i] + [s[i]];
    assert s[..i] + [b] == s[..i+1];
}

lemma multisetEquality(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
   requires m1 > m2 + m3
   requires m1 == m2 + m4
   ensures m3 < m4
{
    // m1 == m2 + m4, m1 > m2 + m3, so m4 > m3
    assert m1 - m2 == m4;
    assert m1 - m2 > m3;
    assert m4 > m3;
    assert m3 < m4;
}

function abs(a: real) : real {if a>0.0 then a else -a}
