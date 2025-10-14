method CountIdenticalItemsInSamePosition<T>(a: seq<T>, b: seq<T>, c: seq<T>) returns (count: nat)
  ensures 0 <= count <= |a| // The result is at most the length of the shortest list
  ensures count == |[i := 0 .. |a|, i < |b| && i < |c| :: a[i] == b[i] && b[i] == c[i]]|
{
  var minLen := if |a| < |b| then if |a| < |c| then |a| else |c| else if |b| < |c| then |b| else |c|;
  count := 0;
  var i := 0;
  while i < minLen
    invariant 0 <= i <= minLen
    invariant 0 <= count <= i
    invariant count == |[j := 0 .. i :: a[j] == b[j] && b[j] == c[j]]|
  {
    if a[i] == b[i] && b[i] == c[i] {
      count := count + 1;
    }
    i := i + 1;
  }
}