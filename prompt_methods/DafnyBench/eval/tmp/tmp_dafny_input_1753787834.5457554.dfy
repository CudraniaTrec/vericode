method foo()
{
  // bar() has ensures false, so this call is unreachable unless the program is inconsistent
  bar();
}

method bar()
  ensures false;
{
  // This method cannot terminate normally; we assert false to make this explicit
  assert false;
}
function abs(a: real) : real {if a>0.0 then a else -a}
