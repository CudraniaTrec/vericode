method FilterOdds(xs: seq<int>) returns (odds: seq<int>)
  ensures forall i :: 0 <= i < |odds| ==> odds[i] % 2 != 0
  ensures forall x :: x in odds ==> x in xs
  ensures forall x :: x in xs && x % 2 != 0 ==> x in odds
{
  odds := xs[..][x => x % 2 != 0];
}