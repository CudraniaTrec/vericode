
method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
{
  // The mapping is injective due to the precondition.
  // The comprehension below is well-defined.
  r:= map k | k in inputs :: f(k) := inputs[k];
  assert forall k :: k in inputs ==> r[f(k)] == inputs[k];
  assert forall k :: k in inputs <==> f(k) in r;
}

function abs(a: real) : real {if a>0.0 then a else -a}
