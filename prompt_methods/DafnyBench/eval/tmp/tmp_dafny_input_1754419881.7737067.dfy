method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    // ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
{
    var n := intSeq.Length;
    if n <= 1 {
        return;
    }

    // Local partition method
    var stack := new int[2 * n];
    var top := 0;
    stack[top] := 0; top := top + 1;
    stack[top] := n; top := top + 1;
    while top > 0
        invariant 0 <= top <= 2 * n
        invariant top % 2 == 0
        invariant forall k :: 0 <= k < top/2 ==> 0 <= stack[2*k] <= stack[2*k+1] <= n
        invariant multiset(intSeq[..]) == multiset(old(intSeq[..]))
    {
        top := top - 1; var r := stack[top];
        top := top - 1; var l := stack[top];
        if r - l <= 1 {
            // Already sorted
            continue;
        }
        // Partition
        var pivot := intSeq[r-1];
        var i := l;
        var j := l;
        while j < r-1
            invariant l <= i <= j <= r-1
            invariant forall k :: l <= k < i ==> intSeq[k] <= pivot
            invariant forall k :: i <= k < j ==> intSeq[k] > pivot
            invariant multiset(intSeq[l..r]) == multiset(old(intSeq[l..r]))
        {
            if intSeq[j] <= pivot {
                var tmp := intSeq[i];
                intSeq[i] := intSeq[j];
                intSeq[j] := tmp;
                i := i + 1;
            }
            j := j + 1;
        }
        var tmp2 := intSeq[i];
        intSeq[i] := intSeq[r-1];
        intSeq[r-1] := tmp2;
        // Now intSeq[i] == pivot
        // Push subarrays to stack
        stack[top] := l; top := top + 1;
        stack[top] := i; top := top + 1;
        stack[top] := i+1; top := top + 1;
        stack[top] := r; top := top + 1;
    }
    // The ensures is only for sortedness, not permutation
}

lemma sort(prevSeq:seq<int>) returns (curSeq:seq<int>)
    ensures (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    ensures multiset(prevSeq) == multiset(curSeq)
{
    if |prevSeq| <= 1 {
        curSeq := prevSeq;
        return;
    }
    var pivot := prevSeq[|prevSeq|-1];
    var left: seq<int> := [];
    var right: seq<int> := [];
    var mid: seq<int> := [];
    var i := 0;
    while i < |prevSeq| - 1
        invariant 0 <= i <= |prevSeq|-1
        invariant left + mid + right + prevSeq[i..|prevSeq|-1] == prevSeq[..|prevSeq|-1]
        invariant forall x:int :: x in left ==> x < pivot
        invariant forall x:int :: x in right ==> x > pivot
        invariant forall x:int :: x in mid ==> x == pivot
        invariant |left| + |mid| + |right| + |prevSeq|-1-i == |prevSeq|-1
    {
        if prevSeq[i] < pivot {
            left := left + [prevSeq[i]];
        } else if prevSeq[i] > pivot {
            right := right + [prevSeq[i]];
        } else {
            mid := mid + [prevSeq[i]];
        }
        i := i + 1;
    }
    mid := mid + [pivot];
    var leftSorted := sort(left);
    var rightSorted := sort(right);
    curSeq := leftSorted + mid + rightSorted;
}

predicate post_sort(prevSeq:seq<int>, curSeq:seq<int>)
{
    (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    && multiset(prevSeq) == multiset(curSeq)
}

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
{
}

lemma twoSortedSequencesWithSameElementsAreEqual(s1:seq<int>, s2:seq<int>)
    requires (forall i:nat, j:nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j])
    requires (forall i:nat, j:nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j])
    requires multiset(s1) == multiset(s2)
    requires |s1| == |s2|
    ensures s1 == s2
{
    if (|s1| != 0) {
        assert s1[|s1|-1] == s2[|s2|-1];
        multisetAdditivity(multiset(s1), multiset([s1[|s1|-1]]), multiset(s1[..|s1|-1]), multiset(s2[..|s2|-1]));
        twoSortedSequencesWithSameElementsAreEqual(s1[..|s1|-1], s2[..|s2|-1]);
    }
}

lemma sort_determinisitc(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
    twoSortedSequencesWithSameElementsAreEqual(curSeq, curSeq');
}

lemma sort_determinisitc1(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires prevSeq == [5,4,3,2,1]
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
    sort_determinisitc(prevSeq, curSeq, curSeq');
}

function abs(a: real) : real {if a>0.0 then a else -a}
