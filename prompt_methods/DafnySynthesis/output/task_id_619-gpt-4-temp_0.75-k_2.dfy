method MoveNumbersToEnd(s: string) returns (result: string)
    ensures |result| == |s|
    ensures multiset(result) == multiset(s)
    ensures forall i :: 0 <= i < |result| ==> 
        (result[i] in '0'..'9' ==> 
            forall j :: 0 <= j < i ==> result[j] !in '0'..'9')
{
    var letters := "";
    var digits := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |letters| + |digits| == i
        invariant multiset(letters + digits) == multiset(s[..i])
        invariant forall j :: 0 <= j < |letters| ==> letters[j] !in '0'..'9'
        invariant forall j :: 0 <= j < |digits| ==> digits[j] in '0'..'9'
    {
        if s[i] in '0'..'9' {
            digits := digits + s[i .. i+1];
        } else {
            letters := letters + s[i .. i+1];
        }
        i := i + 1;
    }
    result := letters + digits;
}