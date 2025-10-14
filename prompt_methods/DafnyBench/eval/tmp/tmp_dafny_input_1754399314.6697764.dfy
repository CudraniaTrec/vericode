
method IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1])
{
  if |x|==0 {
    return true;
  }
  var i := 0;
  var j := |x| - 1;
  result := true;
  while (i < j)
    invariant 0 <= i <= |x|
    invariant -1 <= j < |x|
    invariant j == |x| - i - 1 || j == |x| - i
    invariant result ==> (forall k :: 0 <= k < i ==> x[k] == x[|x| - k - 1])
    invariant result ==> (forall k :: j+1 < k < |x| ==> x[k] == x[|x| - k - 1])
    decreases j - i
  {
    if x[i] != x[j] {
      result := false;
      assert x[i] != x[j];
      return;
    }
    i := i + 1;
    j := j - 1;
  }
}

function abs(a: real) : real {if a>0.0 then a else -a}
