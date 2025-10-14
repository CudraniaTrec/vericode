method ExtractStringsOfSize(strings: seq<string>, size: nat) returns (result: seq<string>)
    ensures result == [s | s := strings, |s| == size]
{
    var temp := [];
    // Iterate over the input sequence
    var i := 0;
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant temp == [s | s := strings[..i], |s| == size]
    {
        if |strings[i]| == size {
            temp := temp + [strings[i]];
        }
        i := i + 1;
    }
    result := temp;
}