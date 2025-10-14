method Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a==b ==> eq==true
  ensures a!=b ==> eq==false
{
  // Strongest possible assertion about the outcome
  if a == b { 
    eq := true; 
    assert eq == (a == b);
    assert a == b ==> eq == true;
  } else { 
    eq := false; 
    assert eq == (a == b);
    assert a != b ==> eq == false;
  }
  assert eq == (a == b);
}
function abs(a: real) : real {if a>0.0 then a else -a}
