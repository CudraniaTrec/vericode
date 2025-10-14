
method M()
{
  // assert false; // Unreachable, since N() ensures false
  N();
}

method N()
  ensures P();
{
  // Since P() is false, this method cannot terminate normally.
  // assert false; // Unreachable code
  // No code needed; method cannot terminate
  return; // Unreachable, but required for syntax
}

predicate P()
{
  false
}

function abs(a: real) : real {if a>0.0 then a else -a}
