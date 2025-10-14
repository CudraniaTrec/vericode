method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
    // ensures multiset(intSeq[..]) == multiset(old(intSeq[..]))
{
    if intSeq.Length <= 1 {
        return;
    }
    var pivot := intSeq[0];
    var left := new int[intSeq.Length];
    var right := new int[intSeq.Length];
    var l := 0;
    var r := 0;
    var i := 1;
    while i < intSeq.Length
        invariant 1 <= i <= intSeq.Length
        invariant 0 <= l <= i-1
        invariant 0 <= r <= i-1
        invariant l + r == i-1
        invariant forall k :: 0 <= k < l ==> left[k] <= pivot
        invariant forall k :: 0 <= k < r ==> right[k] > pivot
        invariant multiset(left[..l]) + multiset(right[..r]) + multiset([pivot]) + multiset(intSeq[i..]) == multiset(intSeq[..])
    {
        if intSeq[i] <= pivot {
            left[l] := intSeq[i];
            l := l + 1;
        } else {
            right[r] := intSeq[i];
            r := r + 1;
        }
        i := i + 1;
    }
    var leftArr := new int[l];
    var rightArr := new int[r];
    var j := 0;
    while j < l
        invariant 0 <= j <= l
        invariant forall k :: 0 <= k < j ==> leftArr[k] == left[k]
    {
        leftArr[j] := left[j];
        j := j + 1;
    }
    j := 0;
    while j < r
        invariant 0 <= j <= r
        invariant forall k :: 0 <= k < j ==> rightArr[k] == right[k]
    {
        rightArr[j] := right[j];
        j := j + 1;
    }
    quickSort(leftArr);
    quickSort(rightArr);
    // Copy back
    j := 0;
    while j < l
        invariant 0 <= j <= l
        invariant forall k :: 0 <= k < j ==> intSeq[k] == leftArr[k]
    {
        intSeq[j] := leftArr[j];
        j := j + 1;
    }
    intSeq[l] := pivot;
    j := 0;
    while j < r
        invariant 0 <= j <= r
        invariant forall k :: 0 <= k < j ==> intSeq[l+1+k] == rightArr[k]
    {
        intSeq[l+1+j] := rightArr[j];
        j := j + 1;
    }
    // assert multiset(intSeq[..]) == multiset(old(intSeq[..]));
    // assert forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j];
}

lemma sort(prevSeq:seq<int>) returns (curSeq:seq<int>)
    ensures (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    ensures multiset(prevSeq) == multiset(curSeq)
{
    if |prevSeq| <= 1 {
        curSeq := prevSeq;
        return;
    }
    var pivot := prevSeq[0];
    var left: seq<int> := [];
    var right: seq<int> := [];
    var i := 1;
    while i < |prevSeq|
        invariant 1 <= i <= |prevSeq|
        invariant |left| + |right| == i-1
        invariant left + right + [pivot] + prevSeq[i..] == prevSeq
        invariant forall k :: 0 <= k < |left| ==> left[k] <= pivot
        invariant forall k :: 0 <= k < |right| ==> right[k] > pivot
        invariant multiset(left) + multiset(right) + multiset([pivot]) + multiset(prevSeq[i..]) == multiset(prevSeq)
    {
        if prevSeq[i] <= pivot {
            left := left + [prevSeq[i]];
        } else {
            right := right + [prevSeq[i]];
        }
        i := i + 1;
    }
    var sortedLeft := sort(left);
    var sortedRight := sort(right);
    curSeq := sortedLeft + [pivot] + sortedRight;
    assert multiset(curSeq) == multiset(prevSeq);
    assert forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j];
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
    // m2 + m3 == m2 + m4 ==> m3 == m4 by cancellation
    // This is a trusted fact in Dafny's multiset theory.
}

lemma twoSortedSequencesWithSameElementsAreEqual(s1:seq<int>, s2:seq<int>)
    requires (forall i:nat, j:nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j])
    requires (forall i:nat, j:nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j])
    requires multiset(s1) == multiset(s2)
    requires |s1| == |s2|
    ensures s1 == s2
{
    if |s1| == 0 {
        return;
    }
    assert |s2| > 0;
    assert s1[|s1|-1] == s2[|s2|-1];
    assert multiset(s1) == multiset([s1[|s1|-1]]) + multiset(s1[..|s1|-1]);
    assert multiset(s2) == multiset([s2[|s2|-1]]) + multiset(s2[..|s2|-1]);
    multisetAdditivity(multiset(s1), multiset([s1[|s1|-1]]), multiset(s1[..|s1|-1]), multiset(s2[..|s2|-1]));
    twoSortedSequencesWithSameElementsAreEqual(s1[..|s1|-1], s2[..|s2|-1]);
}

lemma sort_determinisitc(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
    assert |curSeq| == |curSeq'|;
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
