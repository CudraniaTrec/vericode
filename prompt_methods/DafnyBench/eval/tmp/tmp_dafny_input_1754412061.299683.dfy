function pow(base: int, exponent: int): int
  requires exponent >= 0
{
  if exponent == 0 then 1
  else if exponent % 2 == 0 then pow(base * base, exponent / 2)
  else base * pow(base, exponent - 1)
}

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
  result := operands[0];
  var i := 0;
  while i < |operators>
    invariant 0 <= i <= |operators|
    invariant |operators| + 1 == |operands|
    invariant forall j :: 0 <= j < |operands| ==> operands[j] >= 0
    invariant operands != []
    invariant operators != []
    decreases |operators| - i
  {
    var op := operators[i];
    i := i + 1;
    match op
    {
      case '+' =>
        result := result + operands[i];
      case '-' =>
        result := result - operands[i];
      case '*' =>
        result := result * operands[i];
      case '/' => 
        if operands[i] != 0 {
            assert operands[i] > 0;
            result := result / operands[i];
        }
      case '^' => 
        assert operands[i] >= 0;
        result := pow(result, operands[i]);
      case _ =>
        assert op != '+' && op != '-' && op != '*' && op != '/' && op != '^';
    }
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
