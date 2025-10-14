
predicate sorted(s : seq<int>) {
  forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
{
  var c, f := 0, v.Length - 1;
  // Invariant: all v[0..c) <= elem, all v(f..v.Length) > elem
  while (c <= f)
    invariant 0 <= c <= v.Length
    invariant -1 <= f < v.Length
    invariant f + 1 >= c
    invariant sorted(v[0..v.Length])
    invariant forall k :: 0 <= k < c ==> v[k] <= elem
    invariant forall k :: f < k < v.Length ==> v[k] > elem
  {
    var m := (c + f) / 2;
    if (v[m] <= elem) {
      c := m + 1;
    } else {
      f := m - 1;
    }
  }
  p := c - 1;
  // Postconditions follow from invariants and assignment to p
}

method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
 ensures b==(elem in v[0..v.Length])
{
  var p := binarySearch(v, elem);
  if (p == -1) {
    b := false;
  } else {
    b := v[p] == elem;
  }
}

method {:tailrecursion false} binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
{
  if (c == f + 1) {
    p := c - 1;
  } else {
    var m := (c + f) / 2;
    if (v[m] <= elem) {
      p := binarySearchRec(v, elem, m + 1, f);
    } else {
      p := binarySearchRec(v, elem, c, m - 1);
    }
  }
}

method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && (forall w::p<=w<v.Length ==> v[w]>elem)
{
  var q := binarySearch(v, elem);
  if (q == -1) {
    b := false;
    p := 0;
  } else if (v[q] == elem) {
    b := true;
    p := q;
  } else {
    b := false;
    p := q + 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
