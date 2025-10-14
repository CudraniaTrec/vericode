method FindLongWords(s: string) returns (words: seq<string>)
{
    var ws := s.Split(" ");
    var result := [];
    var i := 0;
    while i < |ws|
        invariant 0 <= i <= |ws|
        invariant |result| <= i
        invariant forall j :: 0 <= j < |result| ==> |result[j]| >= 4
        invariant forall j :: 0 <= j < i ==> ws[j] in ws ==> (|ws[j]| >= 4 ==> ws[j] in result + [ws[j]])
    {
        if |ws[i]| >= 4 {
            result := result + [ws[i]];
        }
        i := i + 1;
    }
    words := result;
}