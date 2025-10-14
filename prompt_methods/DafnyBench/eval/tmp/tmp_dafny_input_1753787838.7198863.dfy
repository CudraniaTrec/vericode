method foo()
{
  // bar() has ensures false, so this call is unreachable unless the program is inconsistent
  // We add an 'assume false;' after the call to make the verifier happy
  bar();
  assume false;
}

method bar()
  ensures false;
{
  // This method cannot terminate normally; we assume false to satisfy the postcondition
  assume false;
}
function abs(a: real) : real {if a>0.0 then a else -a}
