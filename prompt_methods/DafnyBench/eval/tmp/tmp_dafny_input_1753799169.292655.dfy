function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

lemma sum_plus(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i) + s[i] == sum(s, i+1)
{
    // By definition:
    // sum(s, i+1) == s[0] + sum(s[1..], i) if i+1 > 0 and |s| > 0
    if i == 0 {
        assert sum(s, 0) == 0;
        assert sum(s, 1) == s[0] + sum(s[1..], 0);
        assert sum(s, 1) == s[0];
        assert sum(s, 0) + s[0] == sum(s, 1);
    } else {
        // i > 0
        assert sum(s, i) == s[0] + sum(s[1..], i-1);
        assert sum(s, i+1) == s[0] + sum(s[1..], i);
        sum_plus(s[1..], i-1);
        assert sum(s[1..], i-1) + s[1] == sum(s[1..], i);
        assert sum(s, i) + s[i] == s[0] + sum(s[1..], i-1) + s[i];
        assert sum(s, i) + s[i] == s[0] + (sum(s[1..], i-1) + s[1]);
        assert sum(s, i) + s[i] == s[0] + sum(s[1..], i);
        assert sum(s, i) + s[i] == sum(s, i+1);
    }
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var t := 0;
    var i := 0;
    while i <= |ops|
        invariant 0 <= i <= |ops|
        invariant t == sum(ops, i)
        invariant result <==> exists n: nat :: n < i && sum(ops, n) < 0
        invariant forall n: nat :: n < i ==> sum(ops, n) >= 0
    {
        if i == |ops| {
            break;
        }
        t := t + ops[i];
        sum_plus(ops, i);
        if t < 0 {
            result := true;
            return;
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
