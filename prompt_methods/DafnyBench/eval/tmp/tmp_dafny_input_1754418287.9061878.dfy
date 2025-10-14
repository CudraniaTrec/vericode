
function f(x: int): int

lemma {:axiom} f_positive(x: int)
  requires x >= 0
  ensures f(x) >= 0

lemma f_2_pos()
  ensures f(2) >= 0
{
  // Strongest assertion: f(2) >= 0 by f_positive(2)
  assert 2 >= 0;
  f_positive(2);
  assert f(2) >= 0;
}

lemma f_1_1_pos()
  ensures f(1 + 1) >= 0
{
  // Strongest assertion: 1 + 1 == 2, so f(2) >= 0
  assert 1 + 1 == 2;
  f_2_pos();
  assert f(1 + 1) >= 0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
