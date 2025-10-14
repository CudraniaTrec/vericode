//Dafny Code

method IsLengthOdd(word: string) returns (isOdd: bool)
{
    isOdd := word.Length % 2 == 1;
}