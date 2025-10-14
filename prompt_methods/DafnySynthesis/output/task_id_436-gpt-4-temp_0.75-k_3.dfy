// Dafny Code

method GetNegativeNumbers(arr: array<int>) returns (negatives: seq<int>)
  ensures negatives == [arr[i] | i :: 0 <= i < arr.Length && arr[i] < 0]
{
  var negativesBuilder := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant negativesBuilder == [arr[j] | j :: 0 <= j < i && arr[j] < 0]
  {
    if arr[i] < 0 {
      negativesBuilder := negativesBuilder + [arr[i]];
    }
    i := i + 1;
  }
  negatives := negativesBuilder;
}