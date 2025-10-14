// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 1: Maximum in an array
http://foveoos2011.cost-ic0701.org/verification-competition

Given: A non-empty integer array a.

Verify that the index returned by the method max() given below points to
an element maximal in the array.

public class Max {
    public static int max(int[] a) {
        int x = 0;
        int y = a.length-1;

        while (x != y) {
            if (a[x] <= a[y]) x++;
                else y--;
        }
        return x;
    }
}
*/

method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{
  x := 0;
  var y := a.Length - 1;
  ghost var m := y;
  while x != y
    invariant 0 <= x <= y < a.Length
    invariant forall i :: 0 <= i < x ==> a[i] <= a[m]
    invariant forall i :: y+1 <= i < a.Length ==> a[i] <= a[m]
    invariant m == x || m == y
    decreases y - x
  {
    if a[x] <= a[y] {
      x := x + 1;  m := y;
    } else {
      y := y - 1;  m := x;
    }
  }
  assert 0 <= x < a.Length;
  assert forall i :: 0 <= i < x ==> a[i] <= a[x];
  assert forall i :: x+1 <= i < a.Length ==> a[i] <= a[x];
  return x;
}

function abs(a: real) : real {if a>0.0 then a else -a}
