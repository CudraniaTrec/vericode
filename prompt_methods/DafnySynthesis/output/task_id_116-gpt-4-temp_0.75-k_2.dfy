//Dafny Code

method SeqToInt(seq: seq<int>) returns (result: int)
    requires forall x :: x in seq ==> x > 0
    ensures result >= 0
{
    // Concatenate the digits of each integer in order to form a single integer
    var s := "";
    for i := 0 to |seq| - 1 {
        s := s + seq[i].ToString();
    }
    result := if s == "" then 0 else s as int;
}