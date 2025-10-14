
method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var shrink := numbers;
  var grow := {};
  while |shrink | > 0
    invariant shrink + grow == numbers
    invariant shrink ∩ grow == {}
    invariant grow ⊆ numbers
    invariant shrink ⊆ numbers
    invariant |shrink| + |grow| == |numbers|
    invariant count == |set i | i in grow && i < threshold|
  {
    var i: int :| i in shrink;
    shrink := shrink - {i};
    var grow' := grow+{i};
    grow := grow + {i};
    if i < threshold {
      count := count + 1;
    }
    assert shrink ∩ grow == {};
    assert shrink + grow == numbers;
    assert count == |set j | j in grow && j < threshold|;
  }
  assert shrink == {};
  assert grow == numbers;
  assert count == |set i | i in numbers && i < threshold|;
}

function abs(a: real) : real {if a>0.0 then a else -a}
