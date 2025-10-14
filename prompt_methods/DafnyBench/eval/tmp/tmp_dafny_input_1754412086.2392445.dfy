
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
    // Proof by unfolding the definition of sum
    assert sum(s, i+1) == s[0] + sum(s[1..], i);
    if i == 0 {
        assert sum(s, 0) == 0;
        assert sum(s[1..], 0) == 0;
        assert sum(s, 1) == s[0] + 0;
        assert sum(s, 0) + s[0] == s[0];
    } else {
        assert sum(s, i) == s[0] + sum(s[1..], i-1);
        assert sum(s, i+1) == s[0] + sum(s[1..], i);
        sum_plus(s[1..], i-1);
        assert sum(s[1..], i) == sum(s[1..], i-1) + s[1];
        assert sum(s, i) + s[i] == s[0] + sum(s[1..], i-1) + s[i];
        assert s[i] == s[1..][i-1];
        assert s[0] + sum(s[1..], i-1) + s[1..][i-1] == s[0] + (sum(s[1..], i-1) + s[1..][i-1]);
        assert s[0] + (sum(s[1..], i-1) + s[1..][i-1]) == s[0] + sum(s[1..], i);
        assert sum(s, i) + s[i] == sum(s, i+1);
    }
}

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
{
    result := false;
    var t := 0;
    // Invariant: for all k: nat :: k <= i ==> t == sum(ops, i) && (exists n: nat :: n <= i && sum(ops, n) < 0) <==> result
    var i := 0;
    while i <= |ops|
        invariant 0 <= i <= |ops|
        invariant t == sum(ops, i)
        invariant (exists n: nat :: n <= i && sum(ops, n) < 0) <==> result
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
