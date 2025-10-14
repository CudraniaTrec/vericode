
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
    // from_bits([]) == 0
    assert from_bits(bits(0)) == 0;
    return;
  }
  // bits(n) == [n%2==0?false:true] + bits(n/2)
  // from_bits(bits(n)) == (if n%2==0 then 0 else 1) + 2*from_bits(bits(n/2))
  bits_from_bits(n/2);
  assert from_bits(bits(n)) == (if n%2==0 then 0 else 1) + 2 * from_bits(bits(n/2));
  assert from_bits(bits(n/2)) == n/2;
  assert from_bits(bits(n)) == (if n%2==0 then 0 else 1) + 2 * (n/2);
  // n == 2*(n/2) + (n%2)
  assert n == 2*(n/2) + (n%2);
  assert from_bits(bits(n)) == n;
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{
  if s == [] {
    // from_bits([] + [b]) == from_bits([b]) == (if b then 1 else 0)
    // from_bits([]) == 0
    assert from_bits([b]) == (if b then 1 else 0);
    assert from_bits([] + [b]) == from_bits([]) + exp(2, 0) * (if b then 1 else 0);
    return;
  }
  from_bits_append(s[1..], b);
  // from recursive call:
  // from_bits(s[1..] + [b]) == from_bits(s[1..]) + exp(2, |s[1..]|) * (if b then 1 else 0)
  // from_bits(s) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
  // from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b])
  // Use recursive call and algebra:
  // exp(2, |s|) == 2 * exp(2, |s|-1)
  exp_sum(2, |s|-1, 1);
  assert exp(2, |s|) == 2 * exp(2, |s|-1);
  assert from_bits(s + [b]) == (if s[0] then 1 else 0) + 2 * (from_bits(s[1..]) + exp(2, |s|-1) * (if b then 1 else 0));
  assert from_bits(s + [b]) == ((if s[0] then 1 else 0) + 2 * from_bits(s[1..])) + 2 * exp(2, |s|-1) * (if b then 1 else 0);
  assert from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0);
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
    invariant a == exp(b, from_bits(bits(n0)[..i]))
    invariant c == exp(b, exp(2, i))
    invariant i <= |bits(n0)|
    invariant n == from_bits(bits(n0)[i..])
    invariant |bits(n0)| <= 1 + 64 * n0 // for termination (optional, can be omitted)
    decreases n
  {
    ghost var n_loop_top := n;
    if n % 2 == 1 {
      a := a * c;
      // a' = a * c
      // bits(n0)[i] == true
      // After, a == exp(b, from_bits(bits(n0)[..i])) * exp(b, exp(2, i))
      // But since bits(n0)[i] == true, from_bits(bits(n0)[..i+1]) == from_bits(bits(n0)[..i]) + exp(2, i)
      exp_sum(b, n0-n, i);
      n := n / 2;
      exp_sum_auto(b);
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
      assert bits(n0)[i];
      assert from_bits(bits(n0)[..i+1]) == from_bits(bits(n0)[..i]) + exp(2, i);
      assert a == exp(b, from_bits(bits(n0)[..i+1]));
    } else {
      n := n / 2;
      from_bits_append(bits(n0)[..i], bits(n0)[i]);
      assert !bits(n0)[i];
      assert from_bits(bits(n0)[..i+1]) == from_bits(bits(n0)[..i]);
      // a unchanged
      assert a == exp(b, from_bits(bits(n0)[..i+1]));
    }
    c := c * c;
    exp_sum_auto(b);
    assert c == exp(b, exp(2, i+1));
    i := i + 1;
    assert i <= |bits(n0)|;
    assert n == from_bits(bits(n0)[i..]);
  }
  // After the loop: n == 0, i == |bits(n0)|, a == exp(b, from_bits(bits(n0)[..i])) == exp(b, from_bits(bits(n0)))
  bits_from_bits(n0);
  assert i == |bits(n0)|;
  assert from_bits(bits(n0)[..i]) == from_bits(bits(n0));
  assert a == exp(b, from_bits(bits(n0)));
  assert from_bits(bits(n0)) == n0;
  assert a == exp(b, n0);
  r := a;
}

function abs(a: real) : real {if a>0.0 then a else -a}
