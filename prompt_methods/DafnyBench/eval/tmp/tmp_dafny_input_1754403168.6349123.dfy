method foo()
{
  // The call to bar() is not verifiable since bar's postcondition is 'ensures false'
  // The only way for foo to verify is never to return normally
  assert false;
}

method bar()
  ensures false;
{
  assert false;
}
function abs(a: real) : real {if a>0.0 then a else -a}
