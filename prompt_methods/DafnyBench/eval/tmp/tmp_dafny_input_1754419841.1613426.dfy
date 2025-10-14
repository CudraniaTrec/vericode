method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    // ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
{
    var n := intSeq.Length;
    if n <= 1 {
        return;
    }

    method partition(l:int, r:int) returns (p:int)
        requires 0 <= l < r <= intSeq.Length
        ensures l <= p < r
        ensures forall i:int :: l <= i < p ==> intSeq[i] <= intSeq[p]
        ensures forall i:int :: p < i < r ==> intSeq[i] > intSeq[p]
        ensures multiset(intSeq[l..r]) == multiset(old(intSeq[l..r]))
    {
        var pivot := intSeq[r-1];
        var i := l;
        var j := l;
        while j < r-1
            invariant l <= i <= j <= r-1
            invariant l <= i <= r
            invariant forall k:int :: l <= k < i ==> intSeq[k] <= pivot
            invariant forall k:int :: i <= k < j ==> intSeq[k] > pivot
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
        var tmp := intSeq[i];
        intSeq[i] := intSeq[r-1];
        intSeq[r-1] := tmp;
        p := i;
    }

    method qs(l:int, r:int)
        requires 0 <= l <= r <= intSeq.Length
        modifies intSeq
        ensures forall i:int, j:int | l <= i <= j < r :: intSeq[i] <= intSeq[j]
        ensures multiset(intSeq[l..r]) == multiset(old(intSeq[l..r]))
    {
        if r - l <= 1 {
            return;
        }
        var p := partition(l, r);
        qs(l, p);
        qs(p+1, r);
    }

    qs(0, n);
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
        invariant |left| + |mid| + |right| + |prevSeq| - 1 - i == |prevSeq| - 1
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
    && (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    && multiset(prevSeq) == multiset(curSeq)
}

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
{
    // m2 + m3 == m2 + m4 ==> m3 == m4
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
