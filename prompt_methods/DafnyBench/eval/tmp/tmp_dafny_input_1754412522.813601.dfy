
function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{
  var a, b, c := 0, 1, 2;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == F(i)
    invariant b == F(i+1)
    invariant c == F(i+2)
   {
    a, b, c := b, c, a + c;        
    i := i + 1;
  }
  res := a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
