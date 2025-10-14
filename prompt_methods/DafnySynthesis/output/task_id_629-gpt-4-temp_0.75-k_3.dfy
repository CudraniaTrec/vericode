//Dafny Code

    method FindEvens(arr: array<int>) returns (evens: seq<int>)
        ensures forall i :: 0 <= i < |evens| ==> evens[i] % 2 == 0
        ensures forall x :: x in evens ==> x in arr[..]
    {
        var result := [];
        var i := 0;
        while i < arr.Length
            invariant 0 <= i <= arr.Length
            invariant forall x :: x in result ==> x % 2 == 0
            invariant forall x :: x in result ==> x in arr[..]
        {
            if arr[i] % 2 == 0 {
                result := result + [arr[i]];
            }
            i := i + 1;
        }
        evens := result;
    }