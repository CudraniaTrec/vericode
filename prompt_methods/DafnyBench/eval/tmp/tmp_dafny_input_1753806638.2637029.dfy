// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}

// 1 b)
method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
  res := 0;
  var ind := j-1;

  while ind >= i
    invariant i-1 <= ind <= j-1
    invariant res == sum(a, ind+1, j)
  {
    res := res + a[ind];
    ind := ind - 1;
  }
  assert ind+1 == i;
  assert res == sum(a, i, j);
}

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
{
  var k := i;
  proof(a, 0, j, k);
  r := c[j] - c[i];
  assert r == sum(a, i, j);
}

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}

lemma proof(a: array<int>, i: int, j: int, k:int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
{
  // Induction on j - i
  if i == j {
    // sum(a, i, k) + sum(a, k, j) == 0 + 0 == 0 == sum(a, i, j)
  } else if k == i {
    // sum(a, i, k) == 0, so sum(a, i, k) + sum(a, k, j) == sum(a, k, j) == sum(a, i, j)
  } else if k == j {
    // sum(a, k, j) == 0, so sum(a, i, k) + sum(a, k, j) == sum(a, i, k) == sum(a, i, j)
  } else {
    // Inductive step
    // sum(a, i, j) = a[j-1] + sum(a, i, j-1)
    // sum(a, i, k) + sum(a, k, j) = sum(a, i, k) + (a[j-1] + sum(a, k, j-1))
    // By induction on sum(a, k, j-1)
  }
}

// 2

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
  l := Nil;
  var i := a.Length - 1;
  while i >= 0
    invariant -1 <= i < a.Length
    invariant l == from_array_aux(a, i+1)
  {
    l := Cons(a[i], l);
    i := i - 1;
  }
  assert l == from_array_aux(a, 0);
  assert forall k: int :: 0 <= k < a.Length ==> mem(a[k], l);
  assert forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x;
}

function from_array_aux<T>(a: array<T>, start: int): List<T>
  requires 0 <= start <= a.Length
{
  if start == a.Length then Nil else Cons(a[start], from_array_aux(a, start+1))
}

function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || mem(x, t)
}

function abs(a: real) : real {if a>0.0 then a else -a}
