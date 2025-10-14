
function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if {
        case xs == [] =>
        calc {
            reverse([] + ys);
            calc {
                [] + ys;
                ys;
            }
            reverse(ys);
            reverse(ys) + reverse([]);
        }
        case xs != [] => {
            var zs := xs + ys;
            // strongest possible induction annotation
            // Inductive step: xs = [x] + xs'
            // reverse([x] + xs' + ys) == reverse(ys) + reverse([x] + xs')
            // reverse([x] + xs' + ys) == reverse(xs' + ys) + [x]
            // By IH: reverse(xs' + ys) == reverse(ys) + reverse(xs')
            // So: reverse([x] + xs' + ys) == (reverse(ys) + reverse(xs')) + [x] == reverse(ys) + (reverse(xs') + [x]) == reverse(ys) + reverse([x] + xs')
            assert xs != [];
            assert xs[0] in xs; // for clarity
            assert reverse(xs + ys) == reverse(xs[1..] + ys) + [xs[0]];
            assert reverse(xs[1..] + ys) == reverse(ys) + reverse(xs[1..]); // by induction
            assert reverse(xs + ys) == (reverse(ys) + reverse(xs[1..])) + [xs[0]];
            assert (reverse(ys) + reverse(xs[1..])) + [xs[0]] == reverse(ys) + (reverse(xs[1..]) + [xs[0]]);
            assert reverse(xs) == reverse(xs[1..]) + [xs[0]];
            assert reverse(xs + ys) == reverse(ys) + reverse(xs);
        }
    }
}

lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{
    if {
        case xxs == [] => {}
        case xxs != [] => calc {
            reverse(reverse(xxs));
            ==
            reverse(reverse(xxs[1..]) + [xxs[0]]);
            ==
            { ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]); }
            reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
            ==
            { ReverseInvolution(xxs[1..]); }
            calc {
                reverse([xxs[0]]);
                ==
                [] + [xxs[0]];
                ==
                [xxs[0]];
            }
            [xxs[0]] + xxs[1..];
            ==
            xxs;
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
