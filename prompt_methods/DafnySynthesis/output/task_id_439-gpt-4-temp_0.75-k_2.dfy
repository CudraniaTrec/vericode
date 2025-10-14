// Dafny Code

method JoinArrayToInt(arr: array<int>) returns (result: int)
    requires arr != null
    requires forall i :: 0 <= i < arr.Length ==> 0 <= arr[i] <= 9
    ensures result == (if arr.Length == 0 then 0 else 
                        var r := 0;
                        var i := 0;
                        while i < arr.Length 
                            invariant 0 <= i <= arr.Length
                            invariant r == (if i == 0 then 0 else 
                                            var s := 0;
                                            var j := 0;
                                            while j < i
                                                invariant 0 <= j <= i
                                                invariant s == (if j == 0 then 0 else s*10 + arr[j-1])
                                            {
                                                s := s*10 + arr[j];
                                                j := j + 1;
                                            }
                                            s)
                        {
                            r := r*10 + arr[i];
                            i := i + 1;
                        }
                        r
                      )
{
    result := 0;
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant result == (if i == 0 then 0 else
                             var s := 0;
                             var j := 0;
                             while j < i
                                invariant 0 <= j <= i
                                invariant s == (if j == 0 then 0 else s*10 + arr[j-1])
                             {
                                 s := s*10 + arr[j];
                                 j := j + 1;
                             }
                             s)
    {
        result := result * 10 + arr[i];
        i := i + 1;
    }
}