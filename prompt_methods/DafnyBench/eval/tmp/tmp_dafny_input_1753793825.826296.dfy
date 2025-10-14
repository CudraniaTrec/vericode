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
    var n := a.Length;
    // Outer loop: [0..i) is sorted, [i..n) is a permutation of the original
    for i := 0 to n
        invariant 0 <= i <= n
        invariant Ordered(a, 0, i)
        invariant multiset(a[0..n]) == multiset(old(a[0..n]))
    {
      var minValue := a[i];
      var minPos := i;
      // minPos is the position of the minimum in a[i..j)
      for j := i + 1 to n
          invariant i+1 <= j <= n
          invariant i <= minPos < j
          invariant minValue == a[minPos]
          invariant forall k: int :: i <= k < j ==> a[minPos] <= a[k]
          invariant forall k: int :: i <= k < j ==> a[k] >= minValue
          invariant multiset(a[0..n]) == multiset(old(a[0..n]))
      {
        if a[j] < minValue {
          minValue := a[j];
          minPos := j;
        }
      }
      if i != minPos {
        // swap a[i] and a[minPos]
        var tmp := a[i];
        a[i] := a[minPos];
        a[minPos] := tmp;
      }
      // After swap, [0..i+1) is sorted
      assert Ordered(a, 0, i+1);
      assert multiset(a[0..n]) == multiset(old(a[0..n]));
    }
    assert Ordered(a, 0, n);
    assert multiset(a[0..n]) == multiset(old(a[0..n]));
}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    var n := a.Length;
    for i := 0 to n
        invariant 0 <= i <= n
        invariant Ordered(a, 0, i)
        invariant multiset(a[0..n]) == multiset(old(a[0..n]))
    {
      ghost var minValue := a[i];
      for j := i + 1 to n
          invariant i+1 <= j <= n
          invariant forall k: int :: i <= k < j ==> minValue <= a[k]
          invariant multiset(a[0..n]) == multiset(old(a[0..n]))
      {
        if a[j] < minValue {
          minValue := a[j];
        }
        if a[j] < a[i] {
            var tmp := a[i];
            a[i] := a[j];
            a[j] := tmp;
            assert multiset(a[0..n]) == multiset(old(a[0..n]));
        } else {
            assert multiset(a[0..n]) == multiset(old(a[0..n]));
        }
      }
      // [0..i+1) is sorted
      assert Ordered(a, 0, i+1);
      assert multiset(a[0..n]) == multiset(old(a[0..n]));
    }
    assert Ordered(a, 0, n);
    assert multiset(a[0..n]) == multiset(old(a[0..n]));
}

function abs(a: real) : real {if a>0.0 then a else -a}
