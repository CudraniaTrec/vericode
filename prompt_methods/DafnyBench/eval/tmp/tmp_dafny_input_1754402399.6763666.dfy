
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
  var i:=1;
  sum:=v[0];
  var lmax:=v[0];
  // Invariant: 0 <= i <= v.Length
  // Invariant: lmax == Max({v[j] | 0 <= j < i})
  // Invariant: sum == peekSum(v, i)
  // Invariant: v.Length > 0
  while(i<v.Length)
    invariant 1 <= i <= v.Length
    invariant lmax == (if i == 0 then 0 else (if i > 0 then (var m := v[0]; var j := 1; while j < i { if v[j] > m { m := v[j]; } j := j + 1; } m) else 0))
    invariant sum == peekSum(v,i)
    invariant v.Length > 0
  {
    if(v[i]>=lmax){
      sum:=sum + v[i];
      lmax:=v[i];
      assert isPeek(v,i);
    }
    i:=i+1;
  }
  assert i == v.Length;
  assert sum == peekSum(v, v.Length);
}

function abs(a: real) : real {if a>0.0 then a else -a}
