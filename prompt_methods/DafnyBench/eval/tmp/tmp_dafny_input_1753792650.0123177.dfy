
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

    var i: int := 0;
    while i < a.Length && (firstEven == -1 || firstOdd == -1)
        invariant 0 <= i <= a.Length
        invariant -1 <= firstEven < a.Length
        invariant -1 <= firstOdd < a.Length
        invariant (firstEven == -1 ==> (forall k :: 0 <= k < i ==> !IsEven(a[k])))
        invariant (firstEven != -1 ==> IsEven(a[firstEven]) && 0 <= firstEven < i && (forall k :: 0 <= k < firstEven ==> !IsEven(a[k])))
        invariant (firstOdd == -1 ==> (forall k :: 0 <= k < i ==> !IsOdd(a[k])))
        invariant (firstOdd != -1 ==> IsOdd(a[firstOdd]) && 0 <= firstOdd < i && (forall k :: 0 <= k < firstOdd ==> !IsOdd(a[k])))
        decreases a.Length - i
    {
        if firstEven == -1 && IsEven(a[i])
        {
            firstEven := i;
        }
        if firstOdd == -1 && IsOdd(a[i])
        {
            firstOdd := i;
        }
        i := i + 1;
    }
    assert firstEven != -1 && firstOdd != -1;
    diff := a[firstEven] - a[firstOdd];
}

function abs(a: real) : real {if a>0.0 then a else -a}
