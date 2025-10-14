ghost function gcd(x:int,y:int):int
  requires x > 0 && y > 0 
  ensures gcd(x, y) > 0
  ensures gcd(x, y) <= x && gcd(x, y) <= y
  ensures x % gcd(x, y) == 0 && y % gcd(x, y) == 0
  ensures forall k :: k > 0 && x % k == 0 && y % k == 0 ==> gcd(x, y) >= k
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
    invariant x + y <= m + n
    invariant gcd(x, y) == gcd(m, n)
    invariant x <= m && y <= n
    decreases if x > y then x - y else y - x
  {
    if x > y { 
      x := x-y; 
      assert x > 0 && y > 0;
      assert gcd(x, y) == gcd(x + y, y);
    } else { 
      y := y-x; 
      assert x > 0 && y > 0;
      assert gcd(x, y) == gcd(x, y + x);
    }
  }
  d := x;
}

ghost function gcd'(x:int,y:int):int
  requires x > 0 && y > 0
  ensures gcd'(x, y) > 0
  ensures gcd'(x, y) <= x && gcd'(x, y) <= y
  ensures x % gcd'(x, y) == 0 && y % gcd'(x, y) == 0
  ensures forall k :: k > 0 && x % k == 0 && y % k == 0 ==> gcd'(x, y) >= k
{
  if x==y then x
  else if x > y then gcd'(x-y,y)
  else gcd'(y,x)
}

function abs(a: real) : real {if a>0.0 then a else -a}
