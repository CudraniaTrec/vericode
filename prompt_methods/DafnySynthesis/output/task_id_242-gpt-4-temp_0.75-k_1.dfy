// Dafny Code

method CountCharacters(s: string) returns (count: int)
    ensures count == |s|
{
    count := s.Length;
}