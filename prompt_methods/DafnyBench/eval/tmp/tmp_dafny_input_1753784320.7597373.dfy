/***************************************
  Dafny Tutorial 2: Sequences and Stacks, Predicates and Assertions

  In this tutorial we introduce a simple stack model using the functional 
  style of programming.
****************************************/
type intStack = seq<int>

function isEmpty(s: intStack): bool
{
    |s| == 0
}

function push(s: intStack, x: int): intStack
{
    s + [x]
}

function pop(s: intStack): intStack
requires !isEmpty(s)
{
   s[..|s|-1] 
}

method testStack() returns (r: intStack)
{
  var s: intStack := [20, 30, 15, 40, 60, 100, 80];

  // Stack should not be empty
  assert !isEmpty(s);

  // Test push
  var s2 := push(s, 5);
  assert |s2| == |s| + 1;
  assert s2[..|s|] == s;
  assert s2[|s|] == 5;

  // Test pop
  var s3 := pop(s2);
  assert s3 == s;

  // Test isEmpty
  var emptyStack: intStack := [];
  assert isEmpty(emptyStack);
  assert !isEmpty(s);

  // Loop to pop all elements
  var t := s2;
  var count := |t|;
  while (!isEmpty(t))
    invariant 0 <= |t| <= count
    decreases |t|
  {
    t := pop(t);
  }
  assert isEmpty(t);

  r:= s;
}

method Main()
{
    var t:=testStack();
    print "Stack tested\nStack is ", t, "\n";
}
function abs(a: real) : real {if a>0.0 then a else -a}
