function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if xs == [] {
        // reverse([] + ys) == reverse(ys) + reverse([])
        calc {
            reverse([] + ys);
            == { }
            reverse(ys);
            == { }
            reverse(ys) + [];
        }
    } else {
        // xs != []
        ReverseAppendDistr(xs[1..], ys);
        // reverse(xs + ys) == reverse(xs[1..] + ys) + [xs[0]]
        // reverse(xs[1..] + ys) == reverse(ys) + reverse(xs[1..])   (by IH)
        // So reverse(xs + ys) == (reverse(ys) + reverse(xs[1..])) + [xs[0]]
        //                        == reverse(ys) + (reverse(xs[1..]) + [xs[0]])
        //                        == reverse(ys) + reverse(xs)
        assert reverse(xs + ys) == reverse(xs[1..] + ys) + [xs[0]];
        assert reverse(xs[1..] + ys) == reverse(ys) + reverse(xs[1..]);
        assert reverse(xs + ys) == (reverse(ys) + reverse(xs[1..])) + [xs[0]];
        assert (reverse(ys) + reverse(xs[1..])) + [xs[0]] == reverse(ys) + (reverse(xs[1..]) + [xs[0]]);
        assert reverse(xs) == reverse(xs[1..]) + [xs[0]];
        assert reverse(xs + ys) == reverse(ys) + reverse(xs);
    }
}

lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{
    if xxs == [] {
        // reverse(reverse([])) == []
    } else {
        ReverseInvolution(xxs[1..]);
        // reverse(reverse(xxs)) == reverse(reverse(xxs[1..]) + [xxs[0]])
        // By ReverseAppendDistr: reverse(a + b) == reverse(b) + reverse(a)
        // So reverse(reverse(xxs[1..]) + [xxs[0]]) == reverse([xxs[0]]) + reverse(reverse(xxs[1..]))
        // reverse([xxs[0]]) == [xxs[0]]
        ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]);
        assert reverse([xxs[0]]) == [xxs[0]];
        assert reverse(reverse(xxs)) == [xxs[0]] + reverse(reverse(xxs[1..]));
        assert reverse(reverse(xxs[1..])) == xxs[1..];
        assert [xxs[0]] + xxs[1..] == xxs;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
