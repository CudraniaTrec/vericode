predicate IsEven (n: int)
{
  n % 2 == 0
}

method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
    var count := 0;
    // First pass: count even numbers
    var i := 0;
    while i < arr.Length
      invariant 0 <= i <= arr.Length
      invariant 0 <= count <= i
      invariant count == |[j | j := 0 .. i, IsEven(arr[j]) ]|
    {
      if IsEven(arr[i]) {
        count := count + 1;
      }
      i := i + 1;
    }

    evenNumbers := new int[count];
    var j := 0;
    i := 0;
    while i < arr.Length
      invariant 0 <= i <= arr.Length
      invariant 0 <= j <= count
      invariant forall k :: 0 <= k < j ==> 0 <= k < evenNumbers.Length && IsEven(evenNumbers[k]) && evenNumbers[k] in arr[..i]
      invariant forall k :: 0 <= k < j ==> exists n :: 0 <= n < i && evenNumbers[k] == arr[n] && IsEven(arr[n])
      invariant forall x :: x in arr[..i] && IsEven(x) ==> x in evenNumbers[..j]
      invariant forall x :: x !in arr[..i] ==> x !in evenNumbers[..j]
    {
      if IsEven(arr[i]) {
        evenNumbers[j] := arr[i];
        j := j + 1;
      }
      i := i + 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
