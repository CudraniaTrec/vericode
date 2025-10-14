//Dafny Code

method FindEvenNumbers(arr: array<int>) returns (evens: seq<int>)
  ensures evens == [arr[i] | i :: 0 <= i < arr.Length && arr[i] % 2 == 0]
{
  var res := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant res == [arr[j] | j :: 0 <= j < i && arr[j] % 2 == 0]
  {
    if arr[i] % 2 == 0 {
      res := res + [arr[i]];
    }
    i := i + 1;
  }
  evens := res;
}