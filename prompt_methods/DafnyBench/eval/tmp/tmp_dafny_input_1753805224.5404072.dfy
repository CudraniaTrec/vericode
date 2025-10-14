
function exp(b: nat, n: nat): nat {
  if n == 0 then 1
  else b * exp(b, n-1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n1 == 0 {
    return;
  }
  exp_sum(b, n1-1, n2);
}

lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  forall n1: nat, n2: nat
    ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2) {
    exp_sum(b, n1, n2);
  }
}

function bits(n: nat): seq<bool>
{
  if n == 0 then []
  else [if (n % 2 == 0) then false else true] + bits(n/2)
}

function from_bits(s: seq<bool>): nat {
  if s == [] then 0
  else (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
}

lemma bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
{
  if n == 0 {
    return;
  }
  var b := if n % 2 == 0 then false else true;
  bits_from_bits(n/2);
  // from_bits([b] + bits(n/2)) == (if b then 1 else 0) + 2 * from_bits(bits(n/2))
  assert from_bits([b] + bits(n/2)) == (if b then 1 else 0) + 2 * from_bits(bits(n/2));
  assert from_bits(bits(n)) == (if b then 1 else 0) + 2 * from_bits(bits(n/2));
  assert (if b then 1 else 0) == n % 2;
  assert n == (n % 2) + 2 * (n / 2);
  assert from_bits(bits(n)) == n;
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    return;
  }
  from_bits_append(s[1..], b);
  assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
  assert from_bits(s) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..]);
  assert exp(2, |s|) == 2 * exp(2, |s|-1);
  // (if b then 1 else 0) * 2 * exp(2, |s|-1) == exp(2, |s|) * (if b then 1 else 0)
  // So:
  // from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var a := 1;
  var c := b;
  var n := n;
  ghost var n0 := n;
  ghost var i: nat := 0;
  bits_from_bits(n);
  while n > 0
    invariant 0 <= n <= n0
    invariant i <= |bits(n0)|
    invariant n == if i == 0 then n0 else n0 / exp(2, i)
    invariant a == exp(b, from_bits(bits(n0)[..i]))
    invariant c == exp(b, exp(2, i))
    decreases n
  {
    if n % 2 == 1 {
      // n > 0, so i < |bits(n0)|
      assert i < |bits(n0)|;
      a := a * c;
      // After this, a == exp(b, from_bits(bits(n0)[..i]) + exp(2, i))
      // But from_bits(bits(n0)[..i+1]) == from_bits(bits(n0)[..i]) + exp(2, i)
      exp_sum(b, from_bits(bits(n0)[..i]), exp(2, i));
      assert from_bits(bits(n0)[..i+1]) == from_bits(bits(n0)[..i]) + exp(2, i);
      a := a; // for Dafny's benefit
    }
    // In both cases, we move to the next bit
    n := n / 2;
    i := i + 1;
    c := c * c;
    exp_sum_auto(b);
  }
  // At loop exit, n == 0, so i == |bits(n0)|
  assert i == |bits(n0)|;
  assert from_bits(bits(n0)[..i]) == n0;
  assert a == exp(b, n0);
  r := a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
