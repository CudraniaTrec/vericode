method ListDifference(xs: seq<int>, ys: seq<int>) returns (diff: seq<int>)
  ensures diff == xs - ys
{
  diff := xs - ys;
}