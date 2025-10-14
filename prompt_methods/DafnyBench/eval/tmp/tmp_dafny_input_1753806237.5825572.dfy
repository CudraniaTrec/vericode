
module Utils {

    lemma AllBelowBoundSize(bound: nat)
        ensures
            var below := set n : nat | n < bound :: n;
            |below| ==  bound
    {
        if bound == 0 {
            assert set n : nat | n < 0 :: n == {};
            assert |set n : nat | n < 0 :: n| == 0;
        } else {
            AllBelowBoundSize(bound-1);
            var belowminus := set n : nat | n < bound-1 :: n;
            var below := set n : nat | n < bound :: n;
            assert below == belowminus + {bound-1};
            assert |below| == |belowminus| + 1;
            assert |belowminus| == bound-1;
            assert |below| == bound;
        }
    }

    lemma SizeOfContainedSet(a: set<nat>, b: set<nat>)
        requires forall n: nat :: n in a ==> n in b
        ensures |a| <= |b|
    {
        if |a| == 0 {
            assert a == {};
            assert |a| == 0;
            assert |a| <= |b|;
        } else {
            var y :| y in a;
            var new_a := a - {y};
            var new_b := b - {y};
            assert y in b;
            assert forall n: nat :: n in new_a ==> n in new_b;
            SizeOfContainedSet(new_a, new_b);
            assert |new_a| <= |new_b|;
            assert |a| == |new_a| + 1;
            assert |b| == |new_b| + 1;
            assert |a| <= |b|;
        }
    }

    lemma BoundedSetSize(bound: nat, values: set<nat>)
        requires forall n :: n in values ==> n < bound
        ensures |values| <= bound
    {
        var all_below_bound := set n : nat | n < bound :: n;
        assert forall n: nat :: n in values ==> n in all_below_bound;
        AllBelowBoundSize(bound);
        SizeOfContainedSet(values, all_below_bound);
        assert |values| <= |all_below_bound|;
        assert |all_below_bound| == bound;
        assert |values| <= bound;
    }

    lemma MappedSetSize<T, U>(s: set<T>, f: T->U, t: set<U>)
        requires forall n: T, m: T :: m != n ==> f(n) != f(m)
        requires t == set n | n in s :: f(n)
        ensures |s| == |t|
    {
        var t := set n | n in s :: f(n);
        if |s| == 0 {
            assert t == {};
            assert |s| == 0;
            assert |t| == 0;
        } else {
            var y :| y in s;
            var new_s := s - {y};
            var new_t := t - {f(y)};
            assert f(y) in t;
            assert forall x: T :: x in new_s ==> f(x) in new_t;
            assert forall x: T :: x in new_s ==> f(x) != f(y);
            assert |new_t| == |new_s|;
            MappedSetSize(new_s, f, new_t);
            assert |new_s| == |new_t|;
            assert |s| == |new_s| + 1;
            assert |t| == |new_t| + 1;
            assert |s| == |t|;
        }
    }

    lemma SetSizes<T>(a: set<T>, b: set<T>, c: set<T>)
        requires c == a + b
        requires forall t: T :: t in a ==> t !in b
        requires forall t: T :: t in b ==> t !in a
        ensures |c| == |a| + |b|
    {
        assert a * b == {};
        assert |a + b| == |a| + |b|;
        assert c == a + b;
        assert |c| == |a| + |b|;
    }

}

function abs(a: real) : real {if a>0.0 then a else -a}
