method foo()
{
  // bar()'s postcondition is ensures false, so this call is impossible to verify
  // Strongest annotation: assert false after the call, but actually, the call itself is impossible
  bar();
  assert false;
}

method bar()
  ensures false;
{
  // This method cannot terminate normally, as its postcondition is false
  assert false;
}
function abs(a: real) : real {if a>0.0 then a else -a}
