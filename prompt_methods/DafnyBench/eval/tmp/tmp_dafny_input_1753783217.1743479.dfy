method Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a==b ==> eq==true
  ensures a!=b ==> eq==false
{
  // Strongest possible: eq == (a == b) always holds
  assert (a == b) ==> (eq == true) || (eq == false);
  if a == b { 
    eq := true; 
    assert eq == (a == b);
  } else { 
    eq := false; 
    assert eq == (a == b);
  }
  assert eq == (a == b);
}
function abs(a: real) : real {if a>0.0 then a else -a}
