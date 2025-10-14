
method M()
{
  N();
  if (*)
  {
    assert (forall b: bool :: b || !b) || 2 != 2;
  }
  else
  {
    assert (forall b: bool :: b || !b) || 2 != 2;
  }
  N();
  if (*)
  {
    assert (forall b: bool :: b || !b) || 2 != 2;
  }
  else
  {
    assert (forall b: bool :: b || !b) || 2 != 2;
  }
}


method N()
  ensures (forall b: bool :: b || !b) || 2 != 2;
{
  // (forall b: bool :: b || !b) is always true, so ensures is trivially satisfied
  assert (forall b: bool :: b || !b);
}

function abs(a: real) : real {if a>0.0 then a else -a}
