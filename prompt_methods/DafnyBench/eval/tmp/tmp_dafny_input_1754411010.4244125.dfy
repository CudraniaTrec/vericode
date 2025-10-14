// Dafny verification of binary search alogirthm from binary_search.py
// Inspired by: https://ece.uwaterloo.ca/~agurfink/stqam/rise4fun-Dafny/#h211

method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
{
    var low, high := 0 , arr.Length-1;
    while low <= high
        invariant 0 <= low <= arr.Length
        invariant -1 <= high < arr.Length
        invariant high < low || (forall i :: 0 <= i < low ==> arr[i] < target)
        invariant high < low || (forall i :: high+1 <= i < arr.Length ==> arr[i] > target)
        invariant high < low || (exists i :: low <= i <= high && arr[i] == target) || not_found(arr, target)
    { 
        var mid := (low + high) / 2;
        assert 0 <= mid < arr.Length;
        if arr[mid] == target
        {
           assert low <= mid <= high;
           return mid;
        }
        else if arr[mid] < target
        {
           assert arr[mid] < target;
           low := mid + 1;
        }
        else
        {
           assert arr[mid] > target;
           high := mid - 1;
        }
    }

    assert not_found(arr, target);
    return -1;
}

// Predicate to check that the array is sorted
predicate sorted(a: array<int>)
reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] 
}

// Predicate to that each element is unique
predicate distinct(arr: array<int>)
    reads arr
{
    forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] != arr[j]
}

// Predicate to that the target is not in the array
predicate not_found(arr: array<int>, target: int)
reads arr
{
    (forall j :: 0 <= j < arr.Length ==> arr[j] != target)
}

// Predicate to that the target is in the array
predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{
    if index == -1 then false
    else if arr[index] == target then true
    else false
}

function abs(a: real) : real {if a>0.0 then a else -a}
