method M()
{
  // Since N()'s postcondition is false, calling N() here is unreachable.
  // No further code is needed or possible.
  N();
}

method N()
  ensures P();
{
  // The postcondition is false, so this method cannot have any terminating execution.
  // Strongest annotation: diverge forever.
  while (true)
    invariant false;
  {
    // unreachable
  }
}

predicate P()
{
  false
}
function abs(a: real) : real {if a>0.0 then a else -a}
