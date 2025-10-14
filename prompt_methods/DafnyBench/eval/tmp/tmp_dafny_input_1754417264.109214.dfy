
function exp(b: nat, n: nat): nat {
  if n == 0 then 1
  else b * exp(b, n-1)
}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n1 == 0 {
    assert exp(b, n1 + n2) == exp(b, 0 + n2);
    assert exp(b, 0 + n2) == exp(b, n2);
    assert exp(b, 0) == 1;
    assert exp(b, n1) == 1;
    assert exp(b, n1) * exp(b, n2) == 1 * exp(b, n2);
    assert exp(b, n1 + n2) == exp(b, n1) * exp(b, n2);
    return;
  } else {
    exp_sum(b, n1-1, n2);
    assert exp(b, n1 + n2) == b * exp(b, (n1-1) + n2);
    assert exp(b, n1) == b * exp(b, n1-1);
    assert exp(b, n1) * exp(b, n2) == (b * exp(b, n1-1)) * exp(b, n2);
    assert exp(b, (n1-1) + n2) == exp(b, n1-1) * exp(b, n2);
    assert exp(b, n1 + n2) == b * (exp(b, n1-1) * exp(b, n2));
    assert exp(b, n1 + n2) == (b * exp(b, n1-1)) * exp(b, n2);
    assert exp(b, n1 + n2) == exp(b, n1) * exp(b, n2);
  }
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
  // Induction on n
  if n == 0 {
    assert bits(0) == [];
    assert from_bits([]) == 0;
    return;
  }
  var b := n % 2 == 1;
  var n2 := n / 2;
  assert bits(n) == [b] + bits(n2);
  bits_from_bits(n2);
  assert from_bits(bits(n)) == (if b then 1 else 0) + 2 * from_bits(bits(n2));
  assert from_bits(bits(n2)) == n2;
  assert (if b then 1 else 0) + 2 * n2 == n;
}

lemma bits_trim_front(n: nat)
  requires n > 0
  ensures from_bits(bits(n)[1..]) == n/2
{
  // bits(n) == [b] + bits(n/2)
  assert bits(n)[1..] == bits(n/2);
  bits_from_bits(n/2);
  assert from_bits(bits(n)[1..]) == from_bits(bits(n/2));
  assert from_bits(bits(n/2)) == n/2;
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    assert from_bits([] + [b]) == from_bits([b]);
    assert from_bits([b]) == (if b then 1 else 0) + 2 * from_bits([]);
    assert from_bits([]) == 0;
    assert exp(2, 0) == 1;
    assert from_bits([b]) == 0 + 1 * (if b then 1 else 0);
    assert from_bits([b]) == (if b then 1 else 0);
    assert from_bits([]) + exp(2, 0) * (if b then 1 else 0) == (if b then 1 else 0);
    return;
  }
  from_bits_append(s[1..], b);
  // from recursive call
  exp_sum(2, |s|-1, 1);
  assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
  assert from_bits(s) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..]);
  assert from_bits(s[1..] + [b]) == from_bits(s[1..]) + exp(2, |s|-1) * (if b then 1 else 0);
  assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * (from_bits(s[1..]) + exp(2, |s|-1) * (if b then 1 else 0));
  assert from_bits(s + [b]) == ((if s[0] then 1 else 0) + 2 * from_bits(s[1..])) + 2 * exp(2, |s|-1) * (if b then 1 else 0);
  assert from_bits(s + [b]) == from_bits(s) + 2 * exp(2, |s|-1) * (if b then 1 else 0);
  assert exp(2, |s|) == 2 * exp(2, |s|-1);
  assert from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0);
}

lemma from_bits_sum(s1: seq<bool>, s2: seq<bool>)
  ensures from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * from_bits(s2)
{
  if s2 == [] {
    assert from_bits(s1 + []) == from_bits(s1);
    assert exp(2, |s1|) * from_bits([]) == 0;
    assert from_bits(s1) + 0 == from_bits(s1);
    return;
  }
  from_bits_sum(s1 + [s2[0]], s2[1..]);
  from_bits_append(s1, s2[0]);
  assert from_bits(s1 + s2) == from_bits(s1 + [s2[0]] + s2[1..]);
  assert s1 + s2 == (s1 + [s2[0]]) + s2[1..];
  assert from_bits(s1 + [s2[0]] + s2[1..]) == from_bits(s1 + [s2[0]]) + exp(2, |s1| + 1) * from_bits(s2[1..]);
  assert from_bits(s1 + [s2[0]]) == from_bits(s1) + exp(2, |s1|) * (if s2[0] then 1 else 0);
  assert from_bits(s1 + s2) == (from_bits(s1) + exp(2, |s1|) * (if s2[0] then 1 else 0)) + exp(2, |s1| + 1) * from_bits(s2[1..]);
  assert exp(2, |s1| + 1) == 2 * exp(2, |s1|);
  assert from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * (if s2[0] then 1 else 0) + 2 * exp(2, |s1|) * from_bits(s2[1..]);
  assert from_bits(s2) == (if s2[0] then 1 else 0) + 2 * from_bits(s2[1..]);
  assert exp(2, |s1|) * from_bits(s2) == exp(2, |s1|) * (if s2[0] then 1 else 0) + exp(2, |s1|) * 2 * from_bits(s2[1..]);
  assert exp(2, |s1|) * 2 == 2 * exp(2, |s1|);
  assert exp(2, |s1|) * from_bits(s2) == exp(2, |s1|) * (if s2[0] then 1 else 0) + 2 * exp(2, |s1|) * from_bits(s2[1..]);
  assert from_bits(s1 + s2) == from_bits(s1) + exp(2, |s1|) * from_bits(s2);
}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var a := 1;
  var c := b;
  ghost var n0 := n;
  var n := n;
  ghost var i: nat := 0;
  bits_from_bits(n);
  while n > 0
    invariant 0 <= n <= n0
    invariant a == exp(b, n0 - n) // a accumulates b^(n0-n)
    invariant c == exp(b, exp(2, i)) // c == b^{2^i}
    invariant i <= |bits(n0)|
    invariant n == from_bits(bits(n0)[i..])
  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      // a accumulates sum(i => b^(2^n_i), i) where n_i are the 1 bits of n
      // TODO: n0-n is sum(i => 2^n_i, i), right?
      a := a * c;
      exp_sum(b, n0-n, i);
      // (n-1)/2 == n/2 in this case, but we want to be extra clear that we're
      // "dropping" a 1 bit here and so something interesting is happening
      n := (n-1) / 2;
      exp_sum_auto(b);
      assert n == from_bits(bits(n0)[i+1..]);
    } else {
      n := n / 2;
      assert n == from_bits(bits(n0)[i+1..]);
    }
    c := c * c;
    exp_sum(b, exp(2, i), exp(2, i));
    // assert bits(n0)[i+1..] == bits(n0)[i..][1..];
    i := i + 1;
  }
  assert n == 0;
  assert a == exp(b, n0 - 0);
  assert a == exp(b, n0);
  return a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
