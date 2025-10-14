method M()
{
  N();
}

method N()
  ensures P();
{
  // Since P() is false, we can use an infinite loop with invariant false && false by contradiction.
  while (true)
    invariant false;
    decreases *; // To satisfy Dafny's requirement for a decreases clause on infinite loops
}

predicate P()
{
  false
}

function abs(a: real) : real {if a>0.0 then a else -a}
