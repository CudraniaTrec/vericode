
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
//   ensures count == |set i | i in numbers && i < threshold|
//   ensures count == |SetLessThan(numbers, threshold)|
{
  count := 0;
  var ss := numbers;
  while ss != {}
    decreases |ss|
    invariant ss <= numbers
    invariant forall x :: x in numbers - ss ==> x < threshold ==> count >= 0
    invariant count == |SetLessThan(numbers, threshold) - SetLessThan(ss, threshold)|
    invariant forall x :: x in numbers - ss ==> (x < threshold ==> x in SetLessThan(numbers, threshold))
    invariant forall x :: x in SetLessThan(numbers, threshold) - SetLessThan(ss, threshold) ==> x in numbers - ss
    invariant forall x :: x in ss ==> x in numbers
    invariant forall x :: x in numbers - ss ==> x < threshold ==> x in SetLessThan(numbers, threshold)
    invariant forall x :: x in SetLessThan(numbers, threshold) ==> x in numbers
    invariant count <= |numbers|
    invariant 0 <= count <= |numbers|
  {
    var i: int :| i in ss;
    ss := ss - {i};
    if i < threshold {
      count := count + 1;
    }
  }
  assert count == |SetLessThan(numbers, threshold)|;
  //   assert count == |set i | i in numbers && i < threshold|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
