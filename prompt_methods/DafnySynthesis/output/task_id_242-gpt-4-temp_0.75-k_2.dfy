//Dafny Code

method CountCharacters(s: string) returns (count: int)
    ensures count == |s|
{
    count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == i
    {
        count := count + 1;
        i := i + 1;
    }
}