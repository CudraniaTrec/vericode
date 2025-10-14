
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
      invariant forall k, k' :: i < k < k' < a.Length ==> a[k] <= a[k']
      invariant 0 <= i < a.Length ==> partitioned(a, i)
      decreases i
    {
        var j := 0;
        while (j < i)
          invariant 0 <= j <= i
          invariant 0 <= i < a.Length
          invariant forall k, k' :: i < k < k' < a.Length ==> a[k] <= a[k']
          invariant forall k :: 0 <= k < j ==> a[k] <= a[k+1]
          decreases i - j
          {
            if(a[j] > a[j+1])
              {
                a[j], a[j+1] := a[j+1], a[j];
                assert a[j] <= a[j+1];
              }
              j := j + 1;
          }
          assert forall k, k' :: i-1 < k < k' < a.Length ==> a[k] <= a[k'];
          i := i -1;
      }
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
