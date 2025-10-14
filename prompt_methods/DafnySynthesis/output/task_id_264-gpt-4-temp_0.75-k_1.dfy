//Dafny Code

method DogYears(humanYears: int) returns (dogYears: int)
    requires humanYears >= 0
    ensures dogYears >= 0
    ensures humanYears == 0 ==> dogYears == 0
    // Common formula: first 2 years = 10.5 dog years each, then 4 dog years per year
{
    if humanYears == 0 {
        dogYears := 0;
    } else if humanYears == 1 {
        dogYears := 10;
        // Some sources use 10.5, but integer result required
    } else if humanYears == 2 {
        dogYears := 21;
    } else {
        dogYears := 21 + 4 * (humanYears - 2);
    }
}