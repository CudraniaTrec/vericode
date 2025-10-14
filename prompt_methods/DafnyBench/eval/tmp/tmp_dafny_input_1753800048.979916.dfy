// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

ghost function f(n: int): int {
  if n < 0 then 0 else 3*f(n-5) + n
}

function pow3(e: int): int
  requires e >= 0
{
  if e == 0 then 1 else 3 * pow3(e - 1)
}

method problem5(n:nat) returns (x: int)
ensures x == f(n)
{
    var a := 1;
    var b := 0;
    var k := n;
    while k >= 0
        invariant 0 <= k + 5
        invariant 0 <= k <= n
        invariant (n - k) % 5 == 0
        invariant a == pow3((n - k) / 5)
        invariant b == 3 * a * f(k - 5) + (a - 1) * k / 2 + (n - k + 5) * (n - k) / 10
    {
        b := a*k + b;
        a := 3*a;
        k := k - 5;
    }
    x := b;
}

function abs(a: real) : real {if a>0.0 then a else -a}
