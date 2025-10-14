
method SquareRoot(N:nat) returns (r:nat)
  ensures r*r <= N < (r+1)*(r+1)
{
  r:=0;
  while (r+1)*(r+1)<=N
    invariant 0 <= r <= N
    invariant r*r <= N
    invariant forall k:nat :: 0 <= k < r ==> k*k <= N
  {
    assert (r+1)*(r+1) <= N;
    r:=r+1;
  }
  assert r*r <= N;
  assert (r+1)*(r+1) > N;
  assert N < (r+1)*(r+1);
}

function abs(a: real) : real {if a>0.0 then a else -a}
