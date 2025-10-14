method splitTwoParts(arr: array<int>, L: int) returns (part1: seq<int>, part2: seq<int>)
  requires arr != null
  requires 0 <= L <= arr.Length
  ensures part1 == arr[0..L]
  ensures part2 == arr[L..]
{
  part1 := arr[0..L];
  part2 := arr[L..];
}