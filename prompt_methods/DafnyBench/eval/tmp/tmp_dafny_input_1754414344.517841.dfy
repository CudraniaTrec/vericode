module Seq {
    export reveals *
    function ToSet<A>(xs: seq<A>): set<A>
        ensures forall x :: x in ToSet(xs) ==> x in xs
        ensures forall x :: x !in ToSet(xs) ==> x !in xs
    {
        if xs == [] then {} else {xs[0]} + ToSet(xs[1..])
    }

    predicate substring1<A(==)>(sub: seq<A>, super: seq<A>) {
        exists k :: 0 <= k < |super| && sub <= super[k..]
    }

    ghost predicate isSubstringAlt<A(!new)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists xs: seq<A> :: IsSuffix(xs, super) && sub <= xs
    }

    predicate isSubstring<A(==)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists k, j :: 0 <= k < j <= |super| && sub == super[k..j]
    }

    lemma SliceOfSliceIsSlice<A>(xs: seq<A>, k: int, j: int, s: int, t: int)
        requires 0 <= k <= j <= |xs|
        requires 0 <= s <= t <= j-k
        ensures xs[k..j][s..t] == xs[(k+s)..(k+s+(t-s))]
    {
        if j-k == 0 {
            assert xs[k..j] == [];
            assert xs[k..j][s..t] == [];
            assert xs[(k+s)..(k+s+(t-s))] == [];
        } else if t-s == 0 {
            assert xs[k..j][s..t] == [];
            assert xs[(k+s)..(k+s+(t-s))] == [];
        } else if t-s > 0 {
            SliceOfSliceIsSlice(xs, k, j, s, t-1);
            assert xs[k..j][s..t] == xs[k..j][s..t-1] + [xs[k..j][t-1]];
            assert xs[(k+s)..(k+s+(t-s))] == xs[(k+s)..(k+s+(t-1-s))] + [xs[k+s+(t-1-s)]];
            assert xs[k..j][t-1] == xs[k+s+(t-1-s)];
        }
    }

    lemma AllSubstringsAreSubstrings<A>(subsub: seq<A>, sub: seq<A>, super: seq<A>)
        requires isSubstring(sub, super)
        requires isSubstring(subsub, sub)
        ensures isSubstring(subsub, super)
    {
        var k, j :| 0 <= k < j <= |super| && sub == super[k..j];
        var s, t :| 0 <= s < t <= |sub| && subsub == sub[s..t];
        assert subsub == super[k..j][s..t];
        if t < j {
            calc {
                subsub;
                super[k..j][s..t];
                {SliceOfSliceIsSlice(super, k, j, s, t);}
                super[(k+s)..(k+s+(t-s))];
            }
            assert 0 <= k+s < k+s+(t-s) <= j <= |super|;
            assert subsub == super[(k+s)..(k+s+(t-s))];
            assert isSubstring(subsub, super);
        } else if t <= j {
            assert 0 <= k+s < k+s+(t-s) <= j <= |super|;
            assert subsub == super[(k+s)..(k+s+(t-s))];
            assert isSubstring(subsub, super);
        }
    }

    predicate IsSuffix<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && xs == ys[|ys| - |xs|..]
    }

    predicate IsPrefix<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && xs == ys[..|xs|]
    }

    lemma PrefixRest<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(xs, ys)
        ensures exists yss: seq<T> :: ys == xs + yss && |yss| == |ys|-|xs|;
    {
        var yss := ys[|xs|..];
        assert ys == xs + yss;
        assert |yss| == |ys| - |xs|;
    }

    lemma IsSuffixReversed<T>(xs: seq<T>, ys: seq<T>)
        requires IsSuffix(xs, ys)
        ensures IsPrefix(reverse(xs), reverse(ys))
    {
        ReverseIndexAll(xs);
        ReverseIndexAll(ys);
        assert |xs| <= |ys|;
        assert xs == ys[|ys| - |xs|..];
        assert reverse(xs) == reverse(ys)[..|xs|];
        assert IsPrefix(reverse(xs), reverse(ys));
    }

    lemma IsPrefixReversed<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(xs, ys)
        ensures IsSuffix(reverse(xs), reverse(ys))
    {
        ReverseIndexAll(xs);
        ReverseIndexAll(ys);
        assert |xs| <= |ys|;
        assert xs == ys[..|xs|];
        assert reverse(xs) == reverse(ys)[|ys|-|xs|..];
        assert IsSuffix(reverse(xs), reverse(ys));
    }

    lemma IsPrefixReversedAll<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(reverse(xs), reverse(ys))
        ensures IsSuffix(reverse(reverse(xs)), reverse(reverse(ys)))
    {
        ReverseIndexAll(xs);
        ReverseIndexAll(ys);
        PrefixRest(reverse(xs), reverse(ys));
        var yss :| reverse(ys) == reverse(xs) + yss && |yss| == |ys|-|xs|;
        reverseReverseIdempotent(ys);
        ReverseConcat(reverse(xs), yss);
        calc {
            reverse(reverse(ys));
            ys;
            reverse(reverse(xs) + yss);
            reverse(yss) + reverse(reverse(xs));
            == {reverseReverseIdempotent(xs);}
            reverse(yss) + xs;
        }
        assert IsSuffix(reverse(reverse(xs)), reverse(reverse(ys)));
    }

    predicate IsSuffix2<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && exists K :: 0 <= K <= |ys|-|xs| && ys == ys[0..K] + xs + ys[(K+|xs|)..]
    }

    function reverse<A>(x: seq<A>): seq<A>
    {
        if x == [] then [] else reverse(x[1..]) + [x[0]]
    }

    lemma {:induction false} reversePreservesMultiset<A>(xs: seq<A>) 
        ensures multiset(xs) == multiset(reverse(xs))
    {
        if xs == [] {
            assert multiset(xs) == multiset(reverse(xs));
        } else {
            var x := xs[0];
            reversePreservesMultiset(xs[1..]);
            assert multiset(reverse(xs)) == multiset(reverse(xs[1..]) + [x]);
            assert multiset(reverse(xs[1..]) + [x]) == multiset(reverse(xs[1..])) + multiset([x]);
            assert multiset([x]) == multiset{x};
            assert multiset(xs) == multiset(xs[1..]) + multiset{x};
            assert multiset(reverse(xs)) == multiset(xs);
        }
    }

    lemma  reversePreservesLength<A>(xs: seq<A>)
        ensures |xs| == |reverse(xs)|
    {
        if xs == [] {
            assert |reverse(xs)| == 0;
        } else {
            reversePreservesLength(xs[1..]);
            assert |reverse(xs)| == |reverse(xs[1..]) + [xs[0]]|;
            assert |reverse(xs[1..]) + [xs[0]]| == |reverse(xs[1..])| + 1;
            assert |reverse(xs[1..])| == |xs[1..]|;
            assert |xs[1..]| == |xs| - 1;
            assert |reverse(xs)| == |xs|;
        }
    }

    lemma  lastReverseIsFirst<A>(xs: seq<A>)
        requires |xs| > 0
        ensures xs[0] == reverse(xs)[|reverse(xs)|-1]
    {
        reversePreservesLength(xs);
        assert |reverse(xs)| == |xs|;
        if |xs| == 1 {
            assert reverse(xs) == xs;
            assert xs[0] == reverse(xs)[0];
        } else {
            reversePreservesLength(xs[1..]);
            assert reverse(xs)[|xs|-1] == xs[0];
        }
    }

    lemma firstReverseIsLast<A>(xs: seq<A>)
        requires |xs| > 0
        ensures reverse(xs)[0] == xs[|xs|-1]
    {
        if |xs| == 1 {
            assert reverse(xs) == xs;
            assert reverse(xs)[0] == xs[0];
            assert xs[|xs|-1] == xs[0];
        } else {
            reversePreservesLength(xs[1..]);
            assert reverse(xs) == reverse(xs[1..]) + [xs[0]];
            assert reverse(xs)[0] == reverse(xs[1..])[0];
            firstReverseIsLast(xs[1..]);
            assert reverse(xs)[0] == xs[1..][|xs[1..]|-1];
            assert xs[1..][|xs[1..]|-1] == xs[|xs|-1];
        }
    }

    lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
        ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
    {
        if |xs| == 0 {
            assert xs + ys == ys;
            assert reverse(xs + ys) == reverse(ys);
            assert reverse(ys) + reverse(xs) == reverse(ys) + [];
            assert reverse(xs + ys) == reverse(ys) + reverse(xs);
        } else {
            ReverseConcat(xs[1..], ys);
            assert reverse(xs + ys) == reverse(xs[1..] + ys) + [xs[0]];
            assert reverse(xs[1..] + ys) == reverse(ys) + reverse(xs[1..]);
            assert reverse(xs + ys) == (reverse(ys) + reverse(xs[1..])) + [xs[0]];
            assert reverse(xs) == reverse(xs[1..]) + [xs[0]];
            assert reverse(xs + ys) == reverse(ys) + (reverse(xs[1..]) + [xs[0]]);
            assert reverse(xs + ys) == reverse(ys) + reverse(xs);
        }
    }

    lemma reverseRest<A>(xs: seq<A>)
        requires |xs| > 0
        ensures reverse(xs) == [xs[ |xs| -1 ] ] + reverse(xs[0..|xs|-1])
    {
        firstReverseIsLast(xs);
        calc {
            reverse(xs);
            reverse(xs[0..|xs|-1] + [xs[|xs|-1]]);
            == {ReverseConcat(xs[0..|xs|-1], [xs[ |xs|-1 ]]);}
            reverse([xs[ |xs|-1 ]]) + reverse(xs[0..|xs|-1]);
        }
        assert reverse([xs[|xs|-1]]) == [xs[|xs|-1]];
        assert reverse(xs) == [xs[|xs|-1]] + reverse(xs[0..|xs|-1]);
    }

    lemma ReverseIndexAll<T>(xs: seq<T>)
        ensures |reverse(xs)| == |xs|
        ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
    {
        reversePreservesLength(xs);
        if xs == [] {
            assert |reverse(xs)| == 0;
        } else {
            reversePreservesLength(xs[1..]);
            ReverseIndexAll(xs[1..]);
            forall i | 0 <= i < |xs|
                ensures reverse(xs)[i] == xs[|xs| - i - 1]
            {
                if i == 0 {
                    firstReverseIsLast(xs);
                    assert reverse(xs)[0] == xs[|xs|-1];
                } else if 1 <= i < |xs| {
                    assert reverse(xs) == reverse(xs[1..]) + [xs[0]];
                    assert reverse(xs)[i] == reverse(xs[1..])[i-1];
                    assert reverse(xs[1..])[i-1] == xs[1..][|xs[1..]|-(i-1)-1];
                    assert xs[1..][|xs[1..]|-(i-1)-1] == xs[|xs|-i-1];
                }
            }
        }
    }

    lemma ReverseIndex<T>(xs: seq<T>, i: int)
        requires 0 <= i < |xs|
        ensures |reverse(xs)| == |xs|
        ensures reverse(xs)[i] == xs[|xs| - i - 1]
    {
        ReverseIndexAll(xs);
    }

    lemma ReverseIndexBack<T>(xs: seq<T>, i: int)
        requires 0 <= i < |xs|
        ensures |reverse(xs)| == |xs|
        ensures reverse(xs)[|xs| - i - 1] == xs[i]
    {
        ReverseIndexAll(xs);
    }

    lemma ReverseSingle<A>(xs: seq<A>) 
        requires |xs| == 1
        ensures reverse(xs) == xs
    {
        assert xs == [xs[0]];
        assert reverse(xs) == reverse([]) + [xs[0]];
        assert reverse([]) == [];
        assert reverse(xs) == [xs[0]];
        assert reverse(xs) == xs;
    }

    lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
        requires |xs| == |ys|
        requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
        ensures xs == ys
    {
        assert xs == ys;
    }

    lemma reverseReverseIdempotent<A>(xs: seq<A>) 
        ensures reverse(reverse(xs)) == xs
    {
        if xs == [] {
            assert reverse(reverse(xs)) == [];
            assert xs == [];
        } else {
            calc {
                reverse(reverse(xs));
                reverse(reverse([xs[0]] + xs[1..]));
                == {ReverseConcat([xs[0]], xs[1..]);}
                reverse(reverse(xs[1..]) + reverse([xs[0]]));
                == {ReverseSingle([xs[0]]);}
                reverse(reverse(xs[1..]) + [xs[0]]);
                == {ReverseConcat(reverse(xs[1..]), [xs[0]]);}
                reverse([xs[0]]) + reverse(reverse(xs[1..]));
                [xs[0]] + reverse(reverse(xs[1..]));
                == {reverseReverseIdempotent(xs[1..]);}
                xs;
            }
        }
    }

    lemma notInNotEqual<A>(xs: seq<A>, elem: A)
        requires elem !in xs
        ensures forall k :: 0 <= k < |xs| ==> xs[k] != elem
    {
        forall k | 0 <= k < |xs| ensures xs[k] != elem {
            assert xs[k] != elem;
        }
    }

    predicate distinct<A(==)>(s: seq<A>) {
        forall x, y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
    }

    lemma distincts<A>(xs: seq<A>, ys: seq<A>)
        requires distinct(xs)
        requires distinct(ys)
        requires forall x :: x in xs ==> x !in ys 
        requires forall y :: y in ys ==> y !in xs 
        ensures distinct(xs+ys)
    {
        var len := |xs + ys|;
        forall x, y | x != y && 0 <= x <= y < |xs+ys|
            ensures (xs+ys)[x] != (xs+ys)[y]
        {
            if 0 <= x < |xs| && 0 <= y < |xs| {
                assert xs[x] != xs[y];
            } else if |xs| <= x < |xs+ys| && |xs| <= y < |xs+ys| {
                assert ys[x - |xs|] != ys[y - |xs|];
            } else if 0 <= x < |xs| && |xs| <= y < |xs+ys| {
                notInNotEqual(ys, xs[x]);
                assert xs[x] != ys[y - |xs|];
            }
        }
    }

    lemma reverseDistinct<A>(list: seq<A>)
        requires distinct(list)
        ensures distinct(reverse(list))
    {
        ReverseIndexAll(list);
        forall x, y | x != y && 0 <= x <= y < |list|
            ensures reverse(list)[x] != reverse(list)[y]
        {
            ReverseIndexAll(list);
            assert reverse(list)[x] == list[|list|-x-1];
            assert reverse(list)[y] == list[|list|-y-1];
            if |list|-x-1 != |list|-y-1 {
                assert list[|list|-x-1] != list[|list|-y-1];
            }
        }
    }

    lemma distinctSplits<A>(list: seq<A>)
        requires distinct(list)
        ensures forall i :: 1 <= i < |list| ==> distinct(list[..i])
    {
        forall i | 1 <= i < |list| ensures distinct(list[..i]) {
            forall x, y | x != y && 0 <= x <= y < i ensures list[..i][x] != list[..i][y] {
                assert list[..i][x] == list[x];
                assert list[..i][y] == list[y];
                assert list[x] != list[y];
            }
        }
    }

    lemma multisetItems<A>(list: seq<A>, item: A)
        requires item in list
        requires multiset(list)[item] > 1
        ensures exists i, j :: 0 <= i < j < |list| && list[i] == item && list[j] == item && i != j
    {
        var k :| 0 <= k < |list| && list[k] == item;
        var rest := list[..k] + list[k+1..];
        assert multiset(rest)[item] == multiset(list)[item] - 1;
        assert multiset(rest)[item] > 0;
        var j :| 0 <= j < |rest| && rest[j] == item;
        var i := k;
        var j2 := if j < k then j else
function abs(a: real) : real {if a>0.0 then a else -a}
