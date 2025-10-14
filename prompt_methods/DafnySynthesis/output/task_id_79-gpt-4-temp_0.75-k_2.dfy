//Dafny Code

method IsWordLengthOdd(word: string) returns (isOdd: bool)
{
    isOdd := word.Length % 2 == 1;
}