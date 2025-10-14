
function min(v:array<int>,i:int):int
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
{
  if (i==1) then v[0]
  else if (v[i-1]<=min(v,i-1)) then v[i-1]
  else min(v,i-1)
}

function countMin(v:array<int>,x:int, i:int):int
 reads v
 requires 0<=i<=v.Length
 ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
{
  if (i==0) then 0
  else if (v[i-1]==x) then 1+countMin(v,x,i-1)
  else countMin(v,x,i-1)
}

method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm 
{
  var i:=1;
  c:=1;
  var mini:=v[0];
  // Invariant: 1 <= i <= v.Length
  // Invariant: mini == min(v, i)
  // Invariant: c == countMin(v, mini, i)
  // Invariant: forall k :: 0 <= k < i ==> v[k] >= mini
  while(i<v.Length)
    invariant 1 <= i <= v.Length
    invariant mini == min(v, i)
    invariant c == countMin(v, mini, i)
    invariant forall k :: 0 <= k < i ==> v[k] >= mini
  {
    if(v[i]==mini){
      c:=c + 1;
      // assert v[i] == mini;
      // assert c == countMin(v, mini, i+1);
    }
    else if(v[i]<mini){
      c:=1;
      mini:=v[i];
      // assert mini == v[i];
      // assert c == 1;
      // assert mini == min(v, i+1);
      // assert c == countMin(v, mini, i+1);
    }
    // else: v[i] > mini, nothing changes
    i:=i+1;
  }
  // assert mini == min(v, v.Length);
  // assert c == countMin(v, mini, v.Length);
}

function abs(a: real) : real {if a>0.0 then a else -a}
