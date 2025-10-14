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
    if |xs| != |ys| {
        // lengths differ
    } else {
        var found := false;
        var i := 0;
        while i < |xs| 
            invariant 0 <= i <= |xs|
            invariant !found ==> (forall j :: 0 <= j < i ==> xs[j] == ys[j])
            decreases |xs| - i
        {
            if xs[i] != ys[i] {
                found := true;
                break;
            }
            i := i + 1;
        }
        if !found {
            assert xs == ys;
        }
    }
}

lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures [someT]+xs != [someT]+ys
{
    if |xs| < |ys| {} else if |ys| > |xs| {}
    else if i: nat :| i < |xs| && i <|ys| && xs[i] != ys[i] {
    }
}

lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusOne(x) !in addOne(ss)
{
    if plusOne(x) in addOne(ss) {
        forall y | y in ss 
            ensures y != x
            ensures plusOne(y) in addOne(ss)
            ensures plusOne(y) != plusOne(x)
        {
            UnequalSeqs(x, y, One);
        }
    }
}

lemma addOneSize(ss: set<seq<Steps>>)
    ensures |addOne(ss)| == |ss|
{
    if ss == {} {
        assert |addOne(ss)| == 0;
    } else {
        var x: seq<Steps> :| x in ss;
        addOneSize(ss - {x});
        plusOneNotIn(ss - {x}, x);
        assert |addOne(ss)| == |addOne(ss - {x})| + 1;
    }
}

lemma addOneSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addOne(ss), sum+1)
{
    forall xs | xs in addOne(ss)
        ensures stepEndsAt(xs, sum+1)
    {
        var x: seq<Steps> :| plusOne(x) == xs && x in ss;
        assert stepSum(xs) == 1 + stepSum(x);
        assert stepSum(x) == sum;
        assert stepSum(xs) == sum+1;
    }
}

lemma endAtNPlus(ss: set<seq<Steps>>, sz: set<seq<Steps>>, sum: nat)
    requires allEndAtN(ss, sum)
    requires allEndAtN(sz, sum)
    ensures allEndAtN(ss+sz, sum)
{
    forall xs | xs in ss+sz ensures stepEndsAt(xs, sum)
    {
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
        forall y | y in ss 
            ensures y != x
            ensures plusTwo(y) in addTwo(ss)
            ensures plusTwo(y) != plusTwo(x)
        {
            UnequalSeqs(x, y, Two);
        }
    }
}

lemma addTwoSize(ss: set<seq<Steps>>)
    ensures |addTwo(ss)| == |ss|
{
    if ss == {} {
        assert |addTwo(ss)| == 0;
    } else {
        var x: seq<Steps> :| x in ss;
        addTwoSize(ss - {x});
        plusTwoNotIn(ss - {x}, x);
        assert |addTwo(ss)| == |addTwo(ss - {x})| + 1;
    }
}

lemma addTwoSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addTwo(ss), sum+2)
{
    forall xs | xs in addTwo(ss)
        ensures stepEndsAt(xs, sum+2)
    {
        var x: seq<Steps> :| plusTwo(x) == xs && x in ss;
        assert stepSum(xs) == 2 + stepSum(x);
        assert stepSum(x) == sum;
        assert stepSum(xs) == sum+2;
    }
}

lemma setSizeAddition<T>(sx: set<T>, sy: set<T>, sz: set<T>) 
    requires sx !! sy
    requires sz == sx + sy
    ensures |sx + sy| == |sx| + |sy|
    ensures |sz| == |sx| + |sy|
{
    assert |sx + sy| == |sx| + |sy|;
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
    var sumSet := stepForward + stepTwoForward;
    assert stepForward !! stepTwoForward;
    setSizeAddition(stepForward, stepTwoForward, sumSet);
    endAtNPlus(stepForward, stepTwoForward, i);
    assert |sumSet| == steps[i-1]+steps[i-2];
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
        invariant forall k: nat :: 0 <= k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
        decreases n - i + 1
    {   
        steps[i] := steps[i-1] + steps[i-2];
        stepSetsAdd(i, steps);
        i := i + 1;
    }
    // At this point, forall k: nat :: 0 <= k < i ==> exists ss: set<seq<Steps>> :: steps[k] == |ss| && allEndAtN(ss, k)
    // For k == n, such an ss exists by the invariant (since i == n+1 after the loop)
    count := steps[n];
    // The ensures clause is satisfied by the loop invariant for k == n
    return count;
}

method Test() {
    var foo := [One, One, Two];
}

function abs(a: real) : real {if a>0.0 then a else -a}
