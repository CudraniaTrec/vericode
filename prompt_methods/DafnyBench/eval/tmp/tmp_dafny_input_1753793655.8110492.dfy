
predicate derangement(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> s[i] != i
}

predicate permutation(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> i in s
}

function multisetRange(n: nat): multiset<nat> {
    multiset(seq(n, i => i))
}

predicate distinct<A(==)>(s: seq<A>) {
    forall x,y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
}

method test() {
    var tests := [2,0,1];
    var tests2 := [0,1,2];
    var t4 := seq(3, i => i);
    var test3 := multisetRange(3);
    // assert !derangement(tests2);
}

method {:timelimit 40} end(links: seq<nat>)
    requires |links| > 0
    requires permutation(links)
    requires derangement(links)
    requires distinct(links)
{
    assume forall x :: x in links ==> 0 <= x < |links|;
    assume forall x :: x in links ==> multiset(links)[x] ==1;
    // assume multiset(links) == multisetRange(|links|);
    var qAct: nat := links[0];
    var i : nat := 0;
    ghost var oldIndex := 0;
    ghost var indices: multiset<nat> := multiset{0};
    ghost var visited: multiset<nat> := multiset{};

    while qAct != 0
        invariant 0 <= i <= |links|
        invariant oldIndex in 0 .. |links|
        invariant indices == multiset(seq(i+1, j => 
            if j == 0 then 0 else links[seqAcc(links, 0, j)]))
        invariant |indices| == i+1
        invariant multiset(visited) == indices
        invariant 0 in indices
        invariant forall x :: x in indices ==> 0 <= x < |links|
        invariant forall x :: x in indices ==> multiset(indices)[x] == 1
        invariant forall x :: x in visited ==> 0 <= x < |links|
        invariant forall x :: x in visited ==> multiset(visited)[x] == 1
        invariant forall x :: x in indices ==> x != seqAcc(links, 0, i) // never revisit
        invariant distinct(links)
        decreases |links| - i
    {
        ghost var oldVisit := visited;
        ghost var oldqAct := qAct;
        ghost var oldOldIndex := oldIndex;
        oldIndex := qAct;
        visited := visited + multiset{qAct};
        indices := indices + multiset{qAct};
            // forall x | x in visited 
            //     ensures exists k :: 0 <= k < |links| && links[k] == x && k in indices
            // {
            //     if x == oldqAct {
            //         // assert links[oldOldIndex] == oldqAct;
            //         // assert exists k :: 0 <= k < |links| && links[k] == x && k in indices;
            //     }else {
            //         // assert x in oldVisit;
            //         // assert exists k :: 0 <= k < |links| && links[k] == x && k in indices;
            //     }
            // }
        //}
        qAct := links[qAct];
        i := i + 1;
    }
}

// Helper function to compute the ith element in the walk starting from 0
function seqAcc(s: seq<nat>, start: nat, n: nat): nat
    requires 0 <= n <= |s|
    requires permutation(s)
    requires derangement(s)
    decreases n
{
    if n == 0 then start else seqAcc(s, s[start], n-1)
}

function abs(a: real) : real {if a>0.0 then a else -a}
