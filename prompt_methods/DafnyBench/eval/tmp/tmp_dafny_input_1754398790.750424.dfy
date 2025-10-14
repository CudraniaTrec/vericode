
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
//   ensures count == |set i | i in numbers && i < threshold|
//   ensures count == |SetLessThan(numbers, threshold)|
{
  count := 0;
  var ss := numbers;
  while ss != {}
    decreases |ss|
    invariant ss <= numbers
    invariant forall x :: x in numbers ==> (x in ss || x in numbers - ss)
    invariant forall x :: x in numbers - ss ==> x < threshold ==> x in numbers
    invariant count == |set i | i in numbers - ss && i < threshold|
    invariant forall x :: x in numbers - ss ==> x < threshold ==> x in numbers
    invariant 0 <= count <= |numbers|
  {
    var i: int :| i in ss;
    ss := ss - {i};
    if i < threshold {
      count := count + 1;
    }
  }
  assert count == |set i | i in numbers && i < threshold|;
  assert count == |SetLessThan(numbers, threshold)|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
