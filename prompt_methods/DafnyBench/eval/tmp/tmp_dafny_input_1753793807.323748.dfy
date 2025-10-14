
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
    // Outer loop invariant: prefix [0..i) is sorted and preserved, suffix [i..n) is a permutation of the original
    for i := 0 to a.Length
        invariant 0 <= i <= n
        invariant Ordered(a, 0, i)
        invariant Preserved(a, 0, n)
        invariant multiset(a[i..n]) == multiset(old(a[i..n]))
    {
      var minValue := a[i];
      var minPos := i;
      // Inner loop invariant: minValue is the minimum of a[i..j), minPos is its position
      for j := i + 1 to a.Length
          invariant i+1 <= j <= n
          invariant i <= minPos < j
          invariant minValue == a[minPos]
          invariant forall k: int :: i <= k < j ==> minValue <= a[k]
          invariant forall k: int :: i <= k < j ==> a[k] >= minValue
          invariant multiset(a[i..n]) == multiset(old(a[i..n]))
      {
        if a[j] < minValue {
          minValue := a[j];
          minPos := j;
        }
      }
      if i != minPos {
        a[i], a[minPos] := minValue, a[i];
        assert multiset(a[i..n]) == multiset(old(a[i..n]));
      }
      assert Ordered(a, 0, i+1);
      assert Preserved(a, 0, n);
    }
    assert Sorted(a);
}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    var n := a.Length;
    // Outer loop invariant: prefix [0..i) is sorted and preserved, suffix [i..n) is a permutation of the original
    for i := 0 to a.Length
        invariant 0 <= i <= n
        invariant Ordered(a, 0, i)
        invariant Preserved(a, 0, n)
        invariant multiset(a[i..n]) == multiset(old(a[i..n]))
    {
      ghost var minValue := a[i];
      // Inner loop invariant: minValue is the minimum of a[i..j)
      for j := i + 1 to a.Length
          invariant i+1 <= j <= n
          invariant forall k: int :: i <= k < j ==> minValue <= a[k]
          invariant multiset(a[i..n]) == multiset(old(a[i..n]))
      {
        label L:
        // assert a[..] == a[0..a.Length];

        if a[j] < minValue {
          minValue := a[j];
        }
        if a[j] < a[i] {
            a[i], a[j] := a[j], a[i];
            assert Preserved(a, 0, n);
        }else{
            assert Preserved(a, 0, n);
        }
      }
      assert Ordered(a, 0, i+1);
      assert Preserved(a, 0, n);
    }
    assert Sorted(a);
}

function abs(a: real) : real {if a>0.0 then a else -a}
