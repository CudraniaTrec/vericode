method foo()
{
  // bar() has ensures false, so this call is unreachable unless the program is inconsistent
  bar();
}

method bar()
  ensures false;
{
  // This method cannot terminate normally; we use 'return;' to indicate non-termination
  // but to satisfy the postcondition, we must diverge
  while (true)
    invariant false;
  {
    // infinite loop, never terminates
  }
}
function abs(a: real) : real {if a>0.0 then a else -a}
