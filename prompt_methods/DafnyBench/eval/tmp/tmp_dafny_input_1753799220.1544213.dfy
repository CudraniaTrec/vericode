
function Sum(n:nat):nat
 
{
  if n==0 then  0 else n + Sum(n-1)
}

method ComputeSum(n:nat) returns (s:nat)
    ensures s ==Sum(n)
{
    s := 0;
    var i := 0;
    while i< n
      invariant 0 <= i <= n
      invariant s == Sum(i)
      decreases n - i
      {
        s := s + i + 1;
        i := i+1;
        assert s == Sum(i);
      }
    assert s == Sum(i);
    assert i == n;
}

function abs(a: real) : real {if a>0.0 then a else -a}
