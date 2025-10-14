// Redo for exam

function gcd(a: nat, b: nat): nat
    decreases b
{
    if b == 0 then a else gcd(b, a % b)
}

lemma r1(a: nat)
    ensures gcd(a, 0) == a
{
}

lemma r2(a:nat)
    ensures gcd(a, a) == a
{
}

lemma r3(a: nat, b: nat)
    ensures gcd(a, b) == gcd(b, a)
{
}

lemma r4 (a: nat, b: nat)
    ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)
{
}

method GCD1(a: int, b: int) returns (r: int)
    requires a > 0 && b > 0
    ensures gcd(a,b) == r
{
    // Strongest possible annotation: measure for termination
    // decreases a + b
    if a < b {
        r3(a,b);
        // gcd(a, b) == gcd(b, a)
        r := GCD1(b, a);
        assert gcd(a, b) == r;
    } else if (a % b == 0) {
        r4(a, b);
        // gcd(a, b) == gcd(b, a % b) == gcd(b, 0)
        r1(b);
        // gcd(b, 0) == b
        r := b;
        assert gcd(a, b) == r;
    } else {
        r4(a, b);
        // gcd(a, b) == gcd(b, a % b)
        // a % b > 0 because a % b != 0 and b > 0
        assert a % b > 0;
        r := GCD1(b, a % b);
        assert gcd(a, b) == r;
    }
}

method GCD2(a: int, b: int) returns (r: int)
    requires a > 0 && b >= 0
    ensures gcd(a,b) == r
{
    // decreases b
    if b == 0 {
        r1(a);
        r := a;
        assert gcd(a, b) == r;
    } else {
        // b > 0
        r4(a, b);
        // gcd(a, b) == gcd(b, a % b)
        assert a % b >= 0;
        r := GCD2(b, a % b);
        assert gcd(a, b) == r;
    }
    assert gcd(a, b) == r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
