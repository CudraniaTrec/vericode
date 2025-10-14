//Dafny Code

method Has31Days(month: int) returns (has31: bool)
    ensures has31 == (month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12)
{
    has31 := month == 1 || month == 3 || month == 5 || month == 7 || month == 8 || month == 10 || month == 12;
}