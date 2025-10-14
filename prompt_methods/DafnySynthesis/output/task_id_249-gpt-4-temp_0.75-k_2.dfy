// Dafny Code

method ArrayIntersection(a: array<int>, b: array<int>) returns (res: array<int>)
  ensures res != null
  ensures forall x :: x in res[..] ==> x in a[..] && x in b[..]
  ensures forall x :: (x in a[..] && x in b[..]) ==> x in res[..]
{
  var temp := new seq<int>[];
  var seen := new set<int>;
  // Put all elements of b in a set for quick lookup
  var bSet := set x | x in b[..] :: x;
  for i := 0 to a.Length - 1 {
    if a[i] in bSet && !(a[i] in seen) {
      temp := temp + [a[i]];
      seen := seen + {a[i]};
    }
  }
  res := new int[temp.Length];
  var idx := 0;
  while idx < temp.Length
    invariant 0 <= idx <= temp.Length
    invariant res != null && res.Length == temp.Length
    invariant forall j :: 0 <= j < idx ==> res[j] == temp[j]
  {
    res[idx] := temp[idx];
    idx := idx + 1;
  }
}