method ReplaceLastWithList(xs: seq<int>, ys: seq<int>) returns (res: seq<int>)
    requires |xs| > 0
{
    // Remove the last element of xs and concatenate ys
    res := xs[..|xs|-1] + ys;
}