method RotateRight(lst: seq<int>, n: int) returns (rotated: seq<int>)
  ensures |rotated| == |lst|
  ensures |lst| == 0 ==> rotated == []
  ensures 0 <= n ==> rotated == lst[|lst|-n % |lst|..] + lst[..|lst|-n % |lst|] ||| |lst| == 0
{
  if |lst| == 0 {
    rotated := [];
    return;
  }
  var len := |lst|;
  var r := n % len;
  if r == 0 {
    rotated := lst;
  } else {
    rotated := lst[len - r ..] + lst[..len - r];
  }
}