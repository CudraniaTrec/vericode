method foo()
{
  // bar()'s postcondition is ensures false, so this call is impossible to verify
  // The only way for this to verify is to make foo unreachable or not return normally
  bar();
  // Unreachable code, no further assertions
}

method bar()
  ensures false;
{
  // This method cannot terminate normally, as its postcondition is false
  assert false;
}
function abs(a: real) : real {if a>0.0 then a else -a}
