method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var shrink := numbers;
  var grow := {};
  while |shrink| > 0
    invariant shrink + grow == numbers
    invariant shrink * grow == {}
    invariant grow <= numbers
    invariant shrink <= numbers
    invariant |shrink| + |grow| == |numbers|
    invariant count == |set i | i in numbers - shrink && i < threshold|
  {
    var i: int :| i in shrink;
    shrink := shrink - {i};
    grow := grow + {i};
    if i < threshold {
      count := count + 1;
    }
  }
  assert shrink == {};
  assert grow == numbers;
  assert count == |set i | i in numbers && i < threshold|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
