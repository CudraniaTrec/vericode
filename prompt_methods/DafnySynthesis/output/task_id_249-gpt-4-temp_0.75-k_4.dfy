//Dafny Code

method ArrayIntersection(a: array<int>, b: array<int>) returns (res: seq<int>)
  ensures forall x :: x in res <==> x in a[..] && x in b[..]
  ensures multiset(res) == multiset([x | x := a[..], x in b[..]])
{
  var setB := set x | x in b[..];
  var intersection := [];
  var seen := set int{};
  // To avoid duplicates in result
  for i := 0 to a.Length - 1
    invariant 0 <= i <= a.Length
    invariant intersection == [a[j] | j := 0 .. i-1, a[j] in setB, a[j] !in seen - {a[j]}]
    invariant seen == set a[j] | j := 0 .. i-1, a[j] in setB
  {
    if a[i] in setB && a[i] !in seen {
      intersection := intersection + [a[i]];
      seen := seen + {a[i]};
    }
  }
  res := intersection;
}