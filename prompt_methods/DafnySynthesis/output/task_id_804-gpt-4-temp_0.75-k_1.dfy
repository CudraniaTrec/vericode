method IsProductEven(arr: array<int>) returns (isEven: bool)
    ensures isEven == (exists i :: 0 <= i < arr.Length && arr[i] % 2 == 0)
{
    isEven := false;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant isEven == (exists j :: 0 <= j < i && arr[j] % 2 == 0)
    {
        if arr[i] % 2 == 0 {
            isEven := true;
            return;
        }
        i := i + 1;
    }
}