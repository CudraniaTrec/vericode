
method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{
  var m,n:=0,0;
  d:=if a[0] < b[0] then (b[0]-a[0]) else (a[0]-b[0]);
  while m<a.Length && n<b.Length
    invariant 0 <= m <= a.Length
    invariant 0 <= n <= b.Length
    invariant d == 
      if m == 0 && n == 0 then (if a[0] < b[0] then (b[0]-a[0]) else (a[0]-b[0]))
      else
        (min { if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]) | 0 <= i < m && 0 <= j < n })
    invariant forall i,j :: 0 <= i < m && 0 <= j < n ==> d <= if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
    decreases a.Length - m + b.Length - n
  {
    var t := if a[m] < b[n] then (b[n]-a[m]) else (a[m]-b[n]);
    d:=if t<d then t else d;
    assert 0 <= m < a.Length && 0 <= n < b.Length;
    if
    case a[m]<=b[n] =>
      m:=m+1;
    case b[n]<=a[m] =>
      n:=n+1;

  }
  // After the loop, m == a.Length || n == b.Length
  // d is the minimum difference found
  assert exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
  assert forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
}

function abs(a: real) : real {if a>0.0 then a else -a}
