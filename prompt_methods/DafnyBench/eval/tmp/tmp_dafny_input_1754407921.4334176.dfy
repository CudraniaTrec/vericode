
twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

ghost predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Sorted(a: array<int>)
    reads a
{
    Ordered(a,0,a.Length) && Preserved(a,0,a.Length)
}

method SelectionnSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    var N := a.Length;
    // Outer loop: i is the current index for placing the next minimum
    var i: int := 0;
    while i < N
        invariant 0 <= i <= N
        invariant Ordered(a, 0, i)
        invariant Preserved(a, 0, N)
    {
      var minValue := a[i];
      var minPos := i;
      var j: int := i + 1;
      // Find the position of the minimum element in a[i..N)
      while j < N
        invariant i+1 <= j <= N
        invariant i < N
        invariant i <= minPos < N
        invariant minValue == a[minPos]
        invariant forall k: int :: i <= k < j ==> a[minPos] <= a[k]
        invariant Preserved(a, 0, N)
      {
        if a[j] < minValue {
          minValue := a[j];
          minPos := j;
        }
        j := j + 1;
      }
      if i != minPos {
        // Swapping a[i] and a[minPos] preserves the multiset
        a[i], a[minPos] := minValue, a[i];
        assert Preserved(a, 0, N);
      }
      i := i + 1;
    }
    assert Ordered(a, 0, N);
    assert Preserved(a, 0, N);
}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    var N := a.Length;
    var i: int := 0;
    while i < N
        invariant 0 <= i <= N
        invariant Ordered(a, 0, i)
        invariant Preserved(a, 0, N)
    {
      ghost var minValue := a[i];
      var j: int := i + 1;
      while j < N
        invariant i+1 <= j <= N
        invariant i < N
        invariant Preserved(a, 0, N)
        invariant minValue == (if exists k: int :: i <= k < j && a[k] < a[i] then a[(min k: int {:trigger a[k]} | i <= k < j && a[k] < a[i])] else a[i])
      {
        label L:
        // assert a[..] == a[0..a.Length];

        if a[j] < minValue {
          minValue := a[j];
        }
        if a[j] < a[i] {
            a[i], a[j] := a[j], a[i];
            assert Preserved(a, 0, N);
        }else{
            assert Preserved(a, 0, N);
        }
        j := j + 1;
      }
      i := i + 1;
    }
    assert Ordered(a, 0, N);
    assert Preserved(a, 0, N);
}

function abs(a: real) : real {if a>0.0 then a else -a}
