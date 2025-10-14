//Dafny Code

method TwoPWords(words: seq<string>) returns (w1: string, w2: string)
    requires |words| >= 2
    requires (|Set x | x in words && x[0..1] == "p"|) >= 2
    ensures w1[0..1] == "p" && w2[0..1] == "p"
{
    var count := 0;
    var res := new string[2];
    var idx := 0;
    while idx < |words| && count < 2
        invariant 0 <= idx <= |words|
        invariant 0 <= count <= 2
        invariant count == |res[..count]|
        invariant forall i :: 0 <= i < count ==> res[i][0..1] == "p"
    {
        if words[idx].|Length| > 0 && words[idx][0..1] == "p" {
            res[count] := words[idx];
            count := count + 1;
        }
        idx := idx + 1;
    }
    w1, w2 := res[0], res[1];
}