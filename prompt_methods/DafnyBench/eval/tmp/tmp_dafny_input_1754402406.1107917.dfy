predicate isPeek(v:array<int>,i:int)
reads v
requires 0<=i<v.Length
{forall k::0<=k<i ==> v[i]>=v[k]}

function peekSum(v:array<int>,i:int):int
reads v
requires 0<=i<=v.Length
{
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
}

method mPeekSum(v:array<int>) returns (sum:int)
requires  v.Length>0
ensures sum==peekSum(v,v.Length)
//Implement and verify an O(v.Length) algorithm to solve this problem
{
  var i := 1;
  sum := v[0];
  var lmax := v[0];
  // Invariants:
  // 0 <= i <= v.Length
  // sum == peekSum(v, i)
  // lmax == Max({v[j] | 0 <= j < i})
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant sum == peekSum(v, i)
    invariant forall j :: 0 <= j < i ==> v[j] <= lmax
    invariant lmax == (if i == 0 then 0 else (var m := v[0]; (forall j :: 0 <= j < i ==> v[j] <= m) && (exists j :: 0 <= j < i && v[j] == m)) ? m : 0)
  {
    if v[i] >= lmax {
      sum := sum + v[i];
      lmax := v[i];
      assert isPeek(v, i);
    }
    i := i + 1;
  }
  assert i == v.Length;
  assert sum == peekSum(v, v.Length);
}

function abs(a: real) : real {if a>0.0 then a else -a}
