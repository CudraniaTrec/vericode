// Dafny Code

method SumEvenAtEvenPositions(arr: array<int>) returns (sum: int)
    requires arr != null
    ensures 0 <= sum
    ensures sum == (if arr.Length == 0 then 0 else 
      (var s: int := 0; 
       var i: int := 0; 
       while i < arr.Length 
         invariant 0 <= i <= arr.Length
         invariant s == (sum j | 0 <= j < i && j % 2 == 0 && arr[j] % 2 == 0 :: arr[j])
       {
         if i % 2 == 0 && arr[i] % 2 == 0 {
           s := s + arr[i];
         }
         i := i + 1;
       }
       s))
{
    sum := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant sum == (sum j | 0 <= j < i && j % 2 == 0 && arr[j] % 2 == 0 :: arr[j])
    {
        if i % 2 == 0 && arr[i] % 2 == 0 {
            sum := sum + arr[i];
        }
        i := i + 1;
    }
}