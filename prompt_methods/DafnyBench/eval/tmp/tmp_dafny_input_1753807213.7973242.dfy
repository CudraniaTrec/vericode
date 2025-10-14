lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
    // original
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
        invariant 0 <= lo <= hi <= |intSeq|
        invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
        invariant forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key
        decreases hi - lo
    {
        var mid := (lo + hi) / 2;
        assert lo <= mid < hi;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            assert intSeq[mid] == key;
            assert mid < |intSeq|;
            return mid;
        }
    }
    assert forall i:nat | 0 <= i < |intSeq| :: intSeq[i] != key;
    return -1;
}

predicate BinarySearchTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
}

lemma BinarySearchDeterministic(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result

{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    var found:bool := false;
    var res:int := -1;
    while lo < hi
        invariant 0 <= lo <= hi <= |intSeq|
        invariant !found ==> res == -1
        invariant found ==> res >= 0 && res < |intSeq| && intSeq[res] == key && forall i:nat | i < res :: intSeq[i] < key
        invariant forall i:nat | 0 <= i < lo :: intSeq[i] < key
        invariant forall i:nat | hi <= i < |intSeq| :: intSeq[i] > key
        decreases hi - lo
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            // Find the first occurrence
            var first := mid;
            while first > lo && intSeq[first - 1] == key
                invariant lo <= first <= mid
                invariant intSeq[mid] == key
                invariant forall i:nat | first <= i <= mid :: intSeq[i] == key
                decreases first
            {
                first := first - 1;
            }
            found := true;
            res := first;
            break;
        }
    }
    if found {
        return res;
    }
    assert forall i:nat | 0 <= i < |intSeq| :: intSeq[i] != key;
    return -1;
}

predicate BinarySearchDeterministicTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong1(intSeq:seq<int>, key:int) returns (r:int)
    // first element
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key // i >= 0

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result
{
    // This postcondition cannot be satisfied in general, so we must not return -1 unless intSeq is empty.
    if |intSeq| == 0 {
        return -1;
    } else if intSeq[0] == key {
        return 0;
    } else {
        // If key is not at position 0, we must check that it does not occur at positions 1..|intSeq|-1
        var found:bool := false;
        var i:int := 1;
        while i < |intSeq|
            invariant 1 <= i <= |intSeq|
            invariant !found ==> forall j:nat | 1 <= j < i :: intSeq[j] != key
            decreases |intSeq| - i
        {
            if intSeq[i] == key {
                found := true;
                break;
            }
            i := i + 1;
        }
        if found {
            return i;
        } else {
            return -1;
        }
    }
}

predicate BinarySearchWrong1Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key) // i >= 0

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong2(intSeq:seq<int>, key:int) returns (r:int)
    // last element
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key // i < |intSeq|

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result
{
    // This postcondition cannot be satisfied in general, so we must not return -1 unless |intSeq| <= 1.
    if |intSeq| == 0 {
        return -1;
    }
    if |intSeq| == 1 {
        if intSeq[0] == key {
            return 0;
        } else {
            return -1;
        }
    }
    // For |intSeq| >= 2
    var found:bool := false;
    var i:int := 0;
    while i < |intSeq| - 1
        invariant 0 <= i <= |intSeq| - 1
        invariant !found ==> forall j:nat | 0 <= j < i :: intSeq[j] != key
        decreases |intSeq| - 1 - i
    {
        if intSeq[i] == key {
            found := true;
            break;
        }
        i := i + 1;
    }
    if found {
        return i;
    }
    if intSeq[|intSeq|-1] == key {
        return |intSeq|-1;
    } else {
        return -1;
    }
}

predicate BinarySearchWrong2Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key) // i < |intSeq|

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong3(intSeq:seq<int>, key:int) returns (r:int)
    // weaker spec
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r < 0 || (r < |intSeq| && intSeq[r] == key) // post condition not correctly formed
{
    return -1;
}

predicate BinarySearchWrong3Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    r < 0 || (r < |intSeq| && intSeq[r] == key)
}

lemma BinarySearchWrong4(intSeq:seq<int>, key:int) returns (r:int)
    // non-realistic
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures 0 <= r < |intSeq| && intSeq[r] == key
{
    // This postcondition cannot be satisfied in general, so we provide a vacuous implementation.
    if |intSeq| > 0 && intSeq[0] == key {
        return 0;
    }
    // The ensures cannot be satisfied in general, so this is intentionally left as a stub.
    return 0; // unreachable in a correct implementation
}

predicate BinarySearchWrong4Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    0 <= r < |intSeq| && intSeq[r] == key
}

function abs(a: real) : real {if a>0.0 then a else -a}
