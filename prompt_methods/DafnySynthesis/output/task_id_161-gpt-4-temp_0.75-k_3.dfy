// Dafny Code

method RemoveElements(a: array<int>, remove: array<int>) returns (result: seq<int>)
  ensures result == [x | x := a[..], x !in remove[..]]
{
  var removeSet := set x | x in remove[..];
  var res := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant res == [x | x := a[..i], x !in removeSet]
  {
    if a[i] !in removeSet {
      res := res + [a[i]];
    }
    i := i + 1;
  }
  result := res;
}