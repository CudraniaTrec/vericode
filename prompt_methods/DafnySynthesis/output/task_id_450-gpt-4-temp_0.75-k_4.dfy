method ExtractStringsOfSize(seq: seq<string>, size: nat) returns (result: seq<string>)
  ensures result == [s | s := seq, |s| == size]
{
  var temp := [];
  for s in seq {
    if |s| == size {
      temp := temp + [s];
    }
  }
  result := temp;
}