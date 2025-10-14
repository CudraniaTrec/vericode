function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if xs == [] {
        calc {
            reverse([] + ys);
            { assert [] + ys == ys; }
            reverse(ys);
            { assert reverse(ys) + reverse([]) == reverse(ys); }
            reverse(ys) + reverse([]);
        }
    } else {
        // xs = [xs[0]] + xs[1..]
        // xs + ys = [xs[0]] + (xs[1..] + ys)
        calc {
            reverse(xs + ys);
            ==
            reverse([xs[0]] + (xs[1..] + ys));
            ==
            reverse(xs[1..] + ys) + [xs[0]];
            ==
            { ReverseAppendDistr(xs[1..], ys); }
            reverse(ys) + reverse(xs[1..]) + [xs[0]];
            ==
            { assert (reverse(ys) + reverse(xs[1..])) + [xs[0]] == reverse(ys) + (reverse(xs[1..]) + [xs[0]]); }
            reverse(ys) + (reverse(xs[1..]) + [xs[0]]);
            ==
            reverse(ys) + reverse(xs);
        }
    }
}

lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{
    if xxs == [] {
        // nothing to prove
    } else {
        calc {
            reverse(reverse(xxs));
            ==
            reverse(reverse(xxs[1..]) + [xxs[0]]);
            ==
            { ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]); }
            reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
            ==
            { ReverseInvolution(xxs[1..]); }
            reverse([xxs[0]]) + xxs[1..];
            ==
            { assert reverse([xxs[0]]) == [xxs[0]]; }
            [xxs[0]] + xxs[1..];
            ==
            xxs;
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
