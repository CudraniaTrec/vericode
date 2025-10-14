
predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

predicate IsFirstEven(evenIndex: int, lst: seq<int>)
    requires 0 <= evenIndex < |lst|
    requires IsEven(lst[evenIndex])
{
    forall i :: 0 <= i < evenIndex ==> IsOdd(lst[i])
}

predicate IsFirstOdd(oddIndex: int, lst: seq<int>)
    requires 0 <= oddIndex < |lst|
    requires IsOdd(lst[oddIndex])
{
    forall i :: 0 <= i < oddIndex ==> IsEven(lst[i])
}


method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: int, oddIndex : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|
    // This is the postcondition that ensures that it's the first, not just any
    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
    var foundEven := false;
    evenIndex := -1;
    // Find first even
    var i: int := 0;
    while i < |lst| && !foundEven
        invariant 0 <= i <= |lst|
        invariant !foundEven ==> evenIndex == -1
        invariant foundEven ==> 0 <= evenIndex < |lst| && IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
        invariant forall j :: 0 <= j < i ==> IsOdd(lst[j])
        decreases |lst| - i
    {
        if IsEven(lst[i])
        {
            evenIndex := i;
            foundEven := true;
            assert IsEven(lst[evenIndex]);
            assert forall j :: 0 <= j < evenIndex ==> IsOdd(lst[j]);
        }
        i := i + 1;
    }
    assert foundEven;
    assert 0 <= evenIndex < |lst|;
    assert IsEven(lst[evenIndex]);
    assert IsFirstEven(evenIndex, lst);

    var foundOdd := false;
    oddIndex := -1;
    // Find first odd
    i := 0;
    while i < |lst| && !foundOdd
        invariant 0 <= i <= |lst|
        invariant !foundOdd ==> oddIndex == -1
        invariant foundOdd ==> 0 <= oddIndex < |lst| && IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
        invariant forall j :: 0 <= j < i ==> IsEven(lst[j])
        decreases |lst| - i
    {
        if IsOdd(lst[i])
        {
            oddIndex := i;
            foundOdd := true;
            assert IsOdd(lst[oddIndex]);
            assert forall j :: 0 <= j < oddIndex ==> IsEven(lst[j]);
        }
        i := i + 1;
    }
    assert foundOdd;
    assert 0 <= oddIndex < |lst|;
    assert IsOdd(lst[oddIndex]);
    assert IsFirstOdd(oddIndex, lst);
}

method ProductEvenOdd(lst: seq<int>) returns (product : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                           0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    assert 0 <= evenIndex < |lst|;
    assert 0 <= oddIndex < |lst|;
    assert IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst);
    assert IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst);
    product := lst[evenIndex] * lst[oddIndex];
    assert exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) &&
                           0 <= j < |lst| && IsOdd(lst[j]) && IsFirstOdd(j, lst) && product == lst[i] * lst[j];
}

function abs(a: real) : real {if a>0.0 then a else -a}
