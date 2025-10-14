// shenanigans going through the dafny tutorial

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{
  more := x + y;
  less := x - y;
  assert less < x;
  assert x < more;
}

method Max(a: int, b: int) returns (c: int)
  ensures a <= c && b <= c
  ensures a == c || b == c
{
  if a > b {
    c := a;
    assert c == a;
    assert c >= b;
  } else { 
    c := b; 
    assert c == b;
    assert c >= a;
  }
  assert a <= c && b <= c;
  assert a == c || b == c;
}

method Testing() {
  var x := Max(3,15);
  assert x == 15;
}

function max(a: int, b: int): int
{
  if a > b then a else b
}
method Testing'() {
}

function abs(x: int): int
{
  if x < 0 then -x else x
}

method Abs(x: int) returns (y: int)
  ensures y == abs(x)
{
  y := abs(x);
  assert y == abs(x);
}

method m(n: nat)
{
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
  assert i == n;
}

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != key
    decreases a.Length - i
  {
    if a[i] == key {return i;}
    i := i+1;
  }
  assert forall k :: 0 <= k < a.Length ==> a[k] != key;
  return -1;
}

method FindMax(a: array<int>) returns (i: int)
  requires a.Length >= 1 
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  i := 0;
  var max := a[i];
  var j := 1;
  while j < a.Length 
    invariant 1 <= j <= a.Length
    invariant 0 <= i < j
    invariant max == a[i]
    invariant forall k :: 0 <= k < j ==> a[k] <= max
    decreases a.Length - j
  {
    if max < a[j] { max := a[j]; i := j; }
    j := j+1;
  }
  assert 0 <= i < a.Length;
  assert forall k :: 0 <= k < a.Length ==> a[k] <= a[i];
}
predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

predicate sorted'(a: array?<int>) // Change the type
  reads a
{
  forall j, k :: a != null && 0 <= j < k < a.Length ==> a[j] <= a[k]
}

function abs(a: real) : real {if a>0.0 then a else -a}
