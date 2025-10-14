method M()
{
  // Since N()'s postcondition is false, calling N() here is unreachable.
  // No code after N() is reachable or verifiable.
  N();
}

method N()
  ensures P();
{
  // Since ensures P() and P() is false, this method cannot terminate normally.
  // Strongest annotation: return immediately, so postcondition is vacuously true.
  return;
}

predicate P()
{
  false
}
function abs(a: real) : real {if a>0.0 then a else -a}
