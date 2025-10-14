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
    evenIndex := -1;
    var i := 0;
    while i < |lst| && evenIndex == -1
        invariant 0 <= i <= |lst|
        invariant -1 <= evenIndex < |lst|
        invariant evenIndex == -1 ==> forall j :: 0 <= j < i ==> IsOdd(lst[j])
        invariant evenIndex != -1 ==> 0 <= evenIndex < i && IsEven(lst[evenIndex]) && forall j :: 0 <= j < evenIndex ==> IsOdd(lst[j])
        decreases |lst| - i
    {
        if IsEven(lst[i]) {
            evenIndex := i;
        }
        i := i + 1;
    }
    // evenIndex found, and is the first even
    assert 0 <= evenIndex < |lst|;
    assert IsEven(lst[evenIndex]);
    assert forall j :: 0 <= j < evenIndex ==> IsOdd(lst[j]);

    oddIndex := -1;
    i := 0;
    while i < |lst| && oddIndex == -1
        invariant 0 <= i <= |lst|
        invariant -1 <= oddIndex < |lst|
        invariant oddIndex == -1 ==> forall j :: 0 <= j < i ==> IsEven(lst[j])
        invariant oddIndex != -1 ==> 0 <= oddIndex < i && IsOdd(lst[oddIndex]) && forall j :: 0 <= j < oddIndex ==> IsEven(lst[j])
        decreases |lst| - i
    {
        if IsOdd(lst[i]) {
            oddIndex := i;
        }
        i := i + 1;
    }
    // oddIndex found, and is the first odd
    assert 0 <= oddIndex < |lst|;
    assert IsOdd(lst[oddIndex]);
    assert forall j :: 0 <= j < oddIndex ==> IsEven(lst[j]);
}

method ProductEvenOdd(lst: seq<int>) returns (product : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                           0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}
function abs(a: real) : real {if a>0.0 then a else -a}
