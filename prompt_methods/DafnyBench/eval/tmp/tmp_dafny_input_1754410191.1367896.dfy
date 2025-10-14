predicate sorted(a: array?<int>, l: int, u: int)
  reads a;
  requires a != null;
  {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
  }
predicate partitioned(a: array?<int>, i: int)
  reads a
  requires a != null
  {
    forall k, k' :: 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
  }

method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
  ensures sorted(a, 0, a.Length-1)
{
  var i := a.Length - 1;
  while(i > 0)
    invariant 0 <= i < a.Length
    invariant forall k, k' :: i < k <= k' < a.Length ==> a[k] <= a[k']
    invariant forall k :: i < k < a.Length ==> forall m :: 0 <= m < k ==> a[m] <= a[k]
    decreases i
  {
    var j := 0;
    while (j < i)
      invariant 0 <= j <= i
      invariant 0 <= i < a.Length
      invariant forall k, k' :: i < k <= k' < a.Length ==> a[k] <= a[k']
      invariant forall m :: 0 <= m < j ==> a[m] <= a[m+1]
      decreases i - j
    {
      if(a[j] > a[j+1])
      {
        a[j], a[j+1] := a[j+1], a[j];
      }
      j := j + 1;
    }
    // After inner loop: a[i] is the largest among a[0..i]
    i := i - 1;
  }
  // After sorting, the whole array is sorted
  assert sorted(a, 0, a.Length-1);
}

method Main() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
  BubbleSort(a);
  var k := 0;
  while(k < 5) { print a[k], "\n"; k := k+1;}
}

function abs(a: real) : real {if a>0.0 then a else -a}
