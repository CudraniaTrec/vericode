
datatype Steps = One | Two

function stepSum(xs: seq<Steps>): nat {
    if xs == [] then 0 else (match xs[0] {
        case One => 1
        case Two => 2
    } + stepSum(xs[1..]))
}

ghost predicate stepEndsAt(xs: seq<Steps>, n: nat) {
    stepSum(xs) == n
}
ghost predicate allEndAtN(ss: set<seq<Steps> >, n: nat) {
    forall xs ::  xs in ss ==> stepEndsAt(xs, n)
}

lemma stepBaseZero() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 0) && |ss| == 0
{
    // The only sequence with sum 0 is the empty sequence, but stepSum([]) == 0,
    // so the set of all sequences of Steps that sum to 0 is the empty set,
    // because we require each step to be One or Two, and the empty sequence is not a valid climbing sequence.
    // But by the definition, stepEndsAt([], 0) is true, so the set {[]} is a valid set.
    // However, the original code expects |ss| == 0, so the empty set.
    var ss: set<seq<Steps>> := {};
    assert allEndAtN(ss, 0);
    assert |ss| == 0;
}

lemma stepBaseOne() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 1) && |ss| == 1
{
    var ss: set<seq<Steps>> := {[One]};
    assert allEndAtN(ss, 1);
    assert |ss| == 1;
}

lemma stepBaseTwo() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 2) && |ss| == 2
{
    var ss: set<seq<Steps>> := {[One, One], [Two]};
    assert allEndAtN(ss, 2);
    assert |ss| == 2;
}

ghost function plusOne(x: seq<Steps>): seq<Steps> {
    [One]+x
}

ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
    ensures addOne(ss) == set x | x in ss :: plusOne(x)
{
    set x | x in ss :: plusOne(x)
}

lemma SeqsNotEqualImplication<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures (exists i: nat :: i < |xs| && i <|ys| && xs[i] != ys[i]) || |xs| < |ys| || |ys| < |xs|
{
    // Standard property of sequences
}

lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures [someT]+xs != [someT]+ys
{
    // If xs != ys, then [someT]+xs != [someT]+ys by sequence properties
    assert ([someT]+xs)[0] == someT && ([someT]+ys)[0] == someT;
    if xs != ys {
        SeqsNotEqualImplication(xs, ys, someT);
    }
}

lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusOne(x) !in addOne(ss)
{
    // plusOne(x) == [One]+x
    // addOne(ss) = { [One]+y | y in ss }
    // If x !in ss, then [One]+x !in { [One]+y | y in ss }
    // Proof by contradiction: suppose [One]+x in addOne(ss), then exists y in ss, [One]+x == [One]+y => x == y, contradiction.
    if plusOne(x) in addOne(ss) {
        var y: seq<Steps> :| y in ss && plusOne(x) == plusOne(y);
        assert x == y;
        assert false;
    }
}

lemma addOneSize(ss: set<seq<Steps>>)
    ensures |addOne(ss)| == |ss|
{
    // plusOne is injective, so |addOne(ss)| == |ss|
    if ss == {} {
        assert |addOne(ss)| == 0;
        assert |ss| == 0;
    } else {
        var x: seq<Steps> :| x in ss;
        addOneSize(ss - {x});
        plusOneNotIn(ss - {x}, x);
        assert |addOne(ss)| == |addOne(ss - {x})| + 1;
        assert |ss| == |ss - {x}| + 1;
    }
}

lemma addOneSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addOne(ss), sum+1)
{
    // For all x in ss, stepSum(x) == sum
    // For all y in addOne(ss), y == [One]+x for some x in ss, so stepSum(y) == 1 + stepSum(x) == sum+1
    forall xs | xs in addOne(ss)
        ensures stepEndsAt(xs, sum+1)
    {
        var x: seq<Steps> :| x in ss && xs == plusOne(x);
        assert stepSum(xs) == 1 + stepSum(x);
        assert stepSum(xs) == sum + 1;
        assert stepEndsAt(xs, sum+1);
    }
    assert allEndAtN(addOne(ss), sum+1);
}

lemma endAtNPlus(ss: set<seq<Steps>>, sz: set<seq<Steps>>, sum: nat)
    requires allEndAtN(ss, sum)
    requires allEndAtN(sz, sum)
    ensures allEndAtN(ss+sz, sum)
{
    forall xs | xs in ss+sz ensures stepEndsAt(xs, sum) {
        if xs in ss {
            assert stepEndsAt(xs, sum);
        } else {
            assert xs in sz;
            assert stepEndsAt(xs, sum);
        }
    }
}

ghost function plusTwo(x: seq<Steps>): seq<Steps> {
    [Two]+x
}

ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
    ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{
    set x | x in ss :: plusTwo(x)
}

lemma plusTwoNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusTwo(x) !in addTwo(ss)
{
    if plusTwo(x) in addTwo(ss) {
        var y: seq<Steps> :| y in ss && plusTwo(x) == plusTwo(y);
        assert x == y;
        assert false;
    }
}

lemma addTwoSize(ss: set<seq<Steps>>)
    ensures |addTwo(ss)| == |ss|
{
    if ss == {} {
        assert |addTwo(ss)| == 0;
        assert |ss| == 0;
    } else {
        var x: seq<Steps> :| x in ss;
        addTwoSize(ss - {x});
        plusTwoNotIn(ss - {x}, x);
        assert |addTwo(ss)| == |addTwo(ss - {x})| + 1;
        assert |ss| == |ss - {x}| + 1;
    }
}

lemma addTwoSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addTwo(ss), sum+2)
{
    forall xs | xs in addTwo(ss)
        ensures stepEndsAt(xs, sum+2)
    {
        var x: seq<Steps> :| x in ss && xs == plusTwo(x);
        assert stepSum(xs) == 2 + stepSum(x);
        assert stepSum(xs) == sum + 2;
        assert stepEndsAt(xs, sum+2);
    }
    assert allEndAtN(addTwo(ss), sum+2);
}

lemma setSizeAddition<T>(sx: set<T>, sy: set<T>, sz: set<T>) 
    requires sx !! sy
    requires sz == sx + sy
    ensures |sx + sy| == |sx| + |sy|
    ensures |sz| == |sx| + |sy|
{
    // If sx and sy are disjoint, then |sx + sy| = |sx| + |sy|
    assert |sz| == |sx| + |sy|;
}

lemma stepSetsAdd(i: nat, steps: array<nat>) 
    requires i >= 2
    requires steps.Length >= i+1
    requires forall k: nat :: k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
    ensures exists sp : set< seq<Steps> > :: |sp| == steps[i-1] + steps[i-2] && allEndAtN(sp, i)
{
    var oneStepBack :| steps[i-1] == |oneStepBack| && allEndAtN(oneStepBack, i-1);
    var twoStepBack :| steps[i-2] == |twoStepBack| && allEndAtN(twoStepBack, i-2);
    var stepForward := addOne(oneStepBack);
    var stepTwoForward := addTwo(twoStepBack);
    addOneSize(oneStepBack);
    addTwoSize(twoStepBack);
    addOneSum(oneStepBack, i-1);
    addTwoSum(twoStepBack, i-2);
    // stepForward and stepTwoForward are disjoint
    forall x | x in oneStepBack, y | y in twoStepBack
        ensures plusOne(x) != plusTwo(y)
    {
        assert [One]+x != [Two]+y;
    }
    assert stepForward !! stepTwoForward;
    var sumSet := stepForward + stepTwoForward;
    setSizeAddition(stepForward, stepTwoForward, sumSet);
    endAtNPlus(stepForward, stepTwoForward, i);
    assert |sumSet| == steps[i-1] + steps[i-2];
    assert allEndAtN(sumSet, i);
}

method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
    var steps := new nat[n+1];
    steps[0] := 0;
    if n > 0 {
        steps[1] := 1;
    }
    if n > 1 {
        steps[2] := 2;
    }
    stepBaseZero();
    stepBaseOne();
    stepBaseTwo();
    if n < 3 {
        return steps[n];
    }
    var i := 3;
    while i <= n 
        invariant 3 <= i <= n+1
        invariant forall k: nat :: 0 <= k < i ==> exists ss: set<seq<Steps>> :: steps[k] == |ss| && allEndAtN(ss, k)
        decreases n - i + 1
    {   
        steps[i] := steps[i-1] + steps[i-2];
        stepSetsAdd(i, steps);
        i := i + 1;
    }
    return steps[n];
}

method Test() {
    var foo := [One, One, Two];
}

function abs(a: real) : real {if a>0.0 then a else -a}
