// Dafny Code

method GetNegativeNumbers(arr: array<int>) returns (negatives: seq<int>)
  ensures negatives == [x | x in arr[..] && x < 0]
{
  var result := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == [arr[j] | j in 0..i-1 && arr[j] < 0]
  {
    if arr[i] < 0 {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
  negatives := result;
}