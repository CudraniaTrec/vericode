function sorted(s : seq<int>) : bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}


// Ex1

method copyArr(a : array<int>, l : int, r : int) returns (ret : array<int>)
  requires 0 <= l < r <= a.Length 
  ensures ret[..] == a[l..r]
{
  var size := r - l;
  ret := new int[size];
  var i := 0;

  while(i < size)
    invariant 0 <= i <= size
    invariant ret[..i] == a[l..l+i]
    invariant ret.Length == size
  {
    ret[i] := a[i + l];
    i := i + 1;
  }
  return;
}


// Ex2

method mergeArr(a : array<int>, l : int, m : int, r : int)
  requires 0 <= l < m < r <= a.Length  
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r]) 
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a 
{
  var left := copyArr(a, l, m);
  var right := copyArr(a, m, r);
  var i := 0;
  var j := 0;
  var cur := l;
  ghost var old_arr := a[..];

  while(cur < r)
    invariant l <= cur <= r
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant i + j == cur - l
    invariant a[..l] == old_arr[..l]
    invariant a[r..] == old_arr[r..]
    invariant forall k :: l <= k < cur ==>
      (if k-l < i then a[k] == left[k-l] else a[k] == right[k-l-i])
    invariant sorted(left[..i])
    invariant sorted(right[..j])
    invariant sorted(a[l..cur])
    invariant multiset(a[l..cur]) == multiset(left[..i] + right[..j])
    decreases r - cur
  {
    if(i == left.Length) {
      a[cur] := right[j];
      j := j + 1;
    } else if(j == right.Length) {
      a[cur] := left[i];
      i := i + 1;
    } else if(left[i] <= right[j]) {
      a[cur] := left[i];
      i := i + 1;
    } else {
      a[cur] := right[j];
      j := j + 1;
    }
    cur := cur + 1;
  }
  // At this point, i == left.Length && j == right.Length && cur == r
  // a[l..r] is filled with all elements from left and right, in sorted order
  return;
}

// Ex3

method sort(a : array<int>) 
  ensures sorted(a[..])
  modifies a
{
  if(a.Length == 0) { return; }
  else { sortAux(a, 0, a.Length); }
}

method sortAux(a : array<int>, l : int, r : int)
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  requires 0 <= l < r <= a.Length
  modifies a
{
  if(l >= (r - 1)) {return;}
  else {
    var m := l + (r - l) / 2;
    sortAux(a, l, m);
    sortAux(a, m, r);
    mergeArr(a, l, m, r);
    return;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
