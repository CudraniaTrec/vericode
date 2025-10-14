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
  bits_from_bits(n/2);
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    return;
  }
  from_bits_append(s[1..], b);
  exp_sum(2, |s|-1, 1);
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
    invariant n == from_bits(if i <= |bits(n0)| then bits(n0)[i..] else [])
    invariant a == exp(b, from_bits(if i <= |bits(n0)| then bits(n0)[..i] else bits(n0)))
    invariant c == exp(b, exp(2, i))
    decreases n
  {
    if i < |bits(n0)| {
      if n % 2 == 1 {
        a := a * c;
      }
      n := n / 2;
      c := c * c;
      i := i + 1;
    } else {
      // Defensive: should never happen, but keeps invariants safe
      n := 0;
    }
  }
  r := a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
