
predicate sorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
{
  var c, f := 0, v.Length-1;
  while (c <= f)
    invariant 0 <= c <= v.Length
    invariant -1 <= f < v.Length
    invariant forall k :: 0 <= k < c ==> v[k] <= elem
    invariant forall k :: f < k < v.Length ==> v[k] > elem
    invariant sorted(v[0..v.Length])
  {
    var m := (c+f)/2;
    if (v[m] <= elem) {
      c := m+1;
    } else {
      f := m-1;
    }
    assert 0 <= c <= v.Length;
    assert -1 <= f < v.Length;
    assert forall k :: 0 <= k < c ==> v[k] <= elem;
    assert forall k :: f < k < v.Length ==> v[k] > elem;
  }
  p := c-1;
  assert -1 <= p < v.Length;
  assert forall u :: 0 <= u <= p ==> v[u] <= elem;
  assert forall w :: p < w < v.Length ==> v[w] > elem;
}

method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
 ensures b==(elem in v[0..v.Length])
 //Implement by calling binary search function
{
  var p := binarySearch(v, elem);
  if(p == -1) {
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
  if (c == f+1) {
    p := c-1;
    assert -1 <= p < v.Length;
    assert forall u :: 0 <= u <= p ==> v[u] <= elem;
    assert forall w :: p < w < v.Length ==> v[w] > elem;
  } else {
    var m := (c+f)/2;
    if (v[m] <= elem) {
      assert 0 <= m+1 <= f+1 <= v.Length;
      assert forall k :: 0 <= k < m+1 ==> v[k] <= elem;
      assert forall k :: f < k < v.Length ==> v[k] > elem;
      p := binarySearchRec(v, elem, m+1, f);
    } else {
      assert 0 <= c <= m-1+1 <= v.Length;
      assert forall k :: 0 <= k < c ==> v[k] <= elem;
      assert forall k :: m-1 < k < v.Length ==> v[k] > elem;
      p := binarySearchRec(v, elem, c, m-1);
    }
    assert -1 <= p < v.Length;
    assert forall u :: 0 <= u <= p ==> v[u] <= elem;
    assert forall w :: p < w < v.Length ==> v[w] > elem;
  }
}

method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && 
               (forall w::p<=w<v.Length ==> v[w]>elem)
 //Implement and verify
{
  p := binarySearch(v, elem);
  if(p == -1) {
    b := false;
    p := p+1;
    assert p == 0;
    assert forall u :: 0 <= u < p ==> v[u] < elem;
    assert forall w :: p <= w < v.Length ==> v[w] > elem;
  } else {
    b := v[p] == elem;
    p := p + if b then 0 else 1;
    if b {
      assert p < v.Length && v[p] == elem;
    } else {
      assert forall u :: 0 <= u < p ==> v[u] < elem;
      assert forall w :: p <= w < v.Length ==> v[w] > elem;
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
