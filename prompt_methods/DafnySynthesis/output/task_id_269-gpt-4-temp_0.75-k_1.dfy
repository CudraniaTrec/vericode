//Dafny Code

method AsciiValue(c: char) returns (ascii: int)
    ensures 0 <= ascii < 0x110000 // char in Dafny is Unicode, but restrict to valid code points
    ensures ascii == c as int
{
    ascii := c as int;
}