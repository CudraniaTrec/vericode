//Bubblesort CS 494 submission
//References: https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny/69365785#69365785

predicate sorted(a:array<int>, from:int, to:int)
  requires a != null; // requires array to have n amount of elements
  reads a; 
  requires 0 <= from <= to <= a.Length; // pre condition checks that from is the start of the range and to is the end of the range, requires values to be within 0 - a.Length
{
  forall x, y :: from <= x < y < to ==> a[x] <= a[y]
}

//helps ensure swapping is valid, it is used inside the nested while loop to make sure linear order is being kept 
predicate pivot(a:array<int>, to:int, pvt:int)
  requires a != null; // requires array to have n amount of elements
  reads a;
  requires 0 <= pvt < to <= a.Length;
{
  forall x, y :: 0 <= x < pvt < y < to ==> a[x] <= a[y] // all values within the array should be in ascending order
}

// Here having the algorithm for the bubblesort

method BubbleSort (a: array<int>)
    requires a != null && a.Length > 0; // makes sure a is not empty and length is greater than 0
    modifies a; // as method runs, we are changing a
    ensures sorted(a, 0, a.Length); // makes sure elements of array a are sorted from 0 - a.Length
    ensures multiset(a[..]) == multiset(old(a[..])); // Since a is being modified, we deference the heap 
                                                      //and compare the previous elements to current elements.
{
  var i := 1;

  while (i < a.Length)
    invariant 1 <= i <= a.Length
    invariant sorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := i;

    while (j > 0)
      invariant 0 <= j <= i
      invariant sorted(a, j, i+1)
      invariant forall k :: j <= k < i ==> a[k-1] <= a[k]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if (a[j-1] > a[j]) {
        a[j - 1], a[j] := a[j], a[j - 1];
      }
      j := j - 1;
    }
    i := i+1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
