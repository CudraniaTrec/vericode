method M()
{
  // Since N() ensures false, this method cannot return normally.
  // So, this method is unreachable after N().
  N();
  // assert false; // Unreachable
}

method N()
  ensures P();
{
  // Since P() is false, this method cannot terminate normally.
  // So, we can make it diverge.
  while (true)
    invariant false;
  // No return needed, as the loop never terminates
}

predicate P()
{
  false
}

function abs(a: real) : real {if a>0.0 then a else -a}
