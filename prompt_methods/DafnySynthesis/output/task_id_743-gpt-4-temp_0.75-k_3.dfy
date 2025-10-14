// Dafny Code

method RotateRight(xs: seq<int>, n: int) returns (rotated: seq<int>)
    ensures |rotated| == |xs|
    ensures rotated == if |xs| == 0 then xs
                       else
                         var shift := if |xs| == 0 then 0 else n % |xs|;
                         xs[|xs| - shift..] + xs[..|xs| - shift]
{
    if |xs| == 0 {
        rotated := xs;
        return;
    }

    var shift := n % |xs|; // handle n > |xs| and n < 0
    if shift < 0 {
        shift := shift + |xs|;
    }

    rotated := xs[|xs| - shift..] + xs[..|xs| - shift];
}