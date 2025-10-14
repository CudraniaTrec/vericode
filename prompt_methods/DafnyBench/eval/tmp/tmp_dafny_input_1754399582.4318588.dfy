
method update_map<K(!new), V>(m1: map<K, V>, m2: map<K, V>) returns (r: map<K, V>)
  ensures (forall k :: k in m2 ==> k in r)
  ensures (forall k :: k in m1 ==> k in r)
  ensures  (forall k :: k in m2 ==> r[k] == m2[k])
  ensures  (forall k :: !(k in m2) && k in m1 ==> r[k] == m1[k])
  ensures  (forall k :: !(k in m2) && !(k in m1) ==> !(k in r))
{
  // r is defined as the union of m1 and m2, with m2 taking precedence
  // Strongest possible annotation: assert all ensures are satisfied
  r:= map k | k in (m1.Keys + m2.Keys) :: if k in m2 then m2[k] else m1[k];

  assert forall k :: k in m2 ==> k in r;
  assert forall k :: k in m1 ==> k in r;
  assert forall k :: k in m2 ==> r[k] == m2[k];
  assert forall k :: !(k in m2) && k in m1 ==> r[k] == m1[k];
  assert forall k :: !(k in m2) && !(k in m1) ==> !(k in r);
}

function abs(a: real) : real {if a>0.0 then a else -a}
