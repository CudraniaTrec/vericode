
method M()
{
  // Since N()'s postcondition is false, calling N() here is unreachable.
  // Strongest annotation: assert false after N() to indicate unreachable code.
  N();
  assert false;
}

method N()
  ensures P();
{
  // Since P() is false, the postcondition can never be satisfied.
  // Strongest annotation: assert false to indicate this.
  assert false;
}

predicate P()
{
  false
}

function abs(a: real) : real {if a>0.0 then a else -a}
