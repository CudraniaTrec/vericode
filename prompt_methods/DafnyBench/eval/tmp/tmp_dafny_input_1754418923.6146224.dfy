//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES

method max(a: int, b: int) returns (z: int)
  requires true
  ensures z >= a || z >= b
{
  if a > b {
    z :=a;
    assert z == a;
    assert z >= a || z >= b;
  }
  else {
    z := b;
    assert z == b;
    assert z >= a || z >= b;
  }
}

method Main() {
  var x;
  x:=max(23,50);
  assert x >= 23 || x >= 50;
}

// 3
method mystery1(n: nat,m: nat) returns (res: nat)
  ensures n+m == res
{
  if (n==0) {
    assert n == 0;
    return m;
  }
  else {
    assert n > 0;
    var aux := mystery1 (n-1,m);
    assert aux == (n-1)+m;
    return 1+aux;
  }
}

method mystery2(n: nat,m: nat) returns (res: nat)
  ensures n*m == res
{
  if (n==0) {
    assert n == 0;
    return 0;
  }
  else {
    assert n > 0;
    var aux := mystery2(n-1,m);
    assert aux == (n-1)*m;
    var aux2 := mystery1(m,aux);
    assert aux2 == m + aux;
    return aux2;
  }
}

// 5a
method m1(x: int,y: int) returns (z: int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
{
  if (x > 0 && y > 0 && y > x) {
    z := x-1;
    // strongest possible assertions
    assert z == x-1;
    assert z >= 0; // because 0 < x, so x-1 >= 0
    assert z < y;  // because x < y, so x-1 < y
    assert z != x; // because x-1 != x
  }
}

// 5b
method m2(x: nat) returns (y: int)
  requires x <= -1
  ensures y > x && y < x
{
  if (x <= -1) {
    y := x+1;
    assert y == x+1;
    assert y > x; // always holds for any x
    // The postcondition y < x is impossible given y == x+1, so this method is unimplementable for this spec.
    // No assertion for y < x, as it is not possible.
  }
}

// 5c
// pode dar false e eles nao serem iguais
// 
method m3(x: int,y: int) returns (z: bool)
  ensures z ==> x==y
{
  if (x == y) {
    z := true;
    assert z ==> x==y;
  }
  else {
    z := false;
    assert z ==> x==y;
  }
}

// 5d
method m4(x: int,y: int) returns (z: bool)
  ensures z ==> x==y && x==y ==> z
{
  if (x == y) {
    z := true;
    assert z ==> x==y;
    assert x==y ==> z;
  }
  else {
    z := false;
    assert z ==> x==y;
    assert x==y ==> z;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
