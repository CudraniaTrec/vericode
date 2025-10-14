ghost function gcd(x:int,y:int):int
  requires x > 0 && y > 0 
  decreases if x > y then x - y else y - x
{
  if x==y then x
  else if x > y then gcd(x-y,y)
  else gcd(x,y-x)
}


method gcdI(m:int, n:int) returns (d:int)
  requires  m > 0 && n > 0
  ensures   d == gcd(m,n) 
{
  var x,y := m,n;
        d := 1;
  while x != y
    invariant x > 0 && y > 0
    invariant gcd(x, y) == gcd(m, n)
    invariant x <= m && y <= n
    decreases x + y
   { if x > y { x := x-y; } else { y := y-x; }
   }
  d := x;
}

ghost function gcd'(x:int,y:int):int
  requires x > 0 && y > 0
  decreases x + y
{
  if x==y then x
  else if x > y then gcd'(x-y,y)
  else gcd'(y,x)
}

function abs(a: real) : real {if a>0.0 then a else -a}
