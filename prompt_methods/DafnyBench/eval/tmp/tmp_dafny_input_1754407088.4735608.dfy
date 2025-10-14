
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
{
    var firstEven: int := -1;
    var firstOdd: int := -1;

    var foundEven: bool := false;
    var foundOdd: bool := false;

    // Loop invariant: 0 <= i <= a.Length
    // Loop invariant: -1 <= firstEven < i || firstEven == -1
    // Loop invariant: -1 <= firstOdd < i || firstOdd == -1
    // Loop invariant: (firstEven == -1 ==> (forall k :: 0 <= k < i ==> !IsEven(a[k])))
    // Loop invariant: (firstEven != -1 ==> IsEven(a[firstEven]) && (forall k :: 0 <= k < firstEven ==> !IsEven(a[k])))
    // Loop invariant: (firstOdd == -1 ==> (forall k :: 0 <= k < i ==> !IsOdd(a[k])))
    // Loop invariant: (firstOdd != -1 ==> IsOdd(a[firstOdd]) && (forall k :: 0 <= k < firstOdd ==> !IsOdd(a[k])))
    // Loop invariant: (firstEven == -1 ==> !foundEven)
    // Loop invariant: (firstOdd == -1 ==> !foundOdd)
    // Loop invariant: (firstEven != -1 ==> foundEven)
    // Loop invariant: (firstOdd != -1 ==> foundOdd)
    // Loop invariant: foundEven ==> (exists k :: 0 <= k < i && IsEven(a[k]))
    // Loop invariant: foundOdd ==> (exists k :: 0 <= k < i && IsOdd(a[k]))
    for i := 0 to a.Length
        invariant 0 <= i <= a.Length
        invariant -1 <= firstEven < i || firstEven == -1
        invariant -1 <= firstOdd < i || firstOdd == -1
        invariant (firstEven == -1 ==> (forall k :: 0 <= k < i ==> !IsEven(a[k])))
        invariant (firstEven != -1 ==> IsEven(a[firstEven]) && (forall k :: 0 <= k < firstEven ==> !IsEven(a[k])))
        invariant (firstOdd == -1 ==> (forall k :: 0 <= k < i ==> !IsOdd(a[k])))
        invariant (firstOdd != -1 ==> IsOdd(a[firstOdd]) && (forall k :: 0 <= k < firstOdd ==> !IsOdd(a[k])))
        invariant (firstEven == -1 ==> !foundEven)
        invariant (firstOdd == -1 ==> !foundOdd)
        invariant (firstEven != -1 ==> foundEven)
        invariant (firstOdd != -1 ==> foundOdd)
        invariant foundEven ==> (exists k :: 0 <= k < i && IsEven(a[k]))
        invariant foundOdd ==> (exists k :: 0 <= k < i && IsOdd(a[k]))
    {
        if firstEven == -1 && IsEven(a[i])
        {
            firstEven := i;
            foundEven := true;
            assert IsEven(a[firstEven]);
            assert forall k :: 0 <= k < firstEven ==> !IsEven(a[k]);
        }
        if firstOdd == -1 && IsOdd(a[i])
        {
            firstOdd := i;
            foundOdd := true;
            assert IsOdd(a[firstOdd]);
            assert forall k :: 0 <= k < firstOdd ==> !IsOdd(a[k]);
        }
        if firstEven != -1 && firstOdd != -1
        {
            break;
        }
    }
    assert 0 <= firstEven < a.Length && 0 <= firstOdd < a.Length;
    assert IsEven(a[firstEven]);
    assert IsOdd(a[firstOdd]);
    assert forall k :: 0 <= k < firstEven ==> IsOdd(a[k]);
    assert forall k :: 0 <= k < firstOdd ==> IsEven(a[k]);
    diff := a[firstEven] - a[firstOdd];
}

function abs(a: real) : real {if a>0.0 then a else -a}
