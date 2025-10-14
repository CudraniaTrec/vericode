//Dafny Code

method MedianLengthOfTrapezium(base1: real, base2: real) returns (median: real)
    requires base1 > 0.0
    requires base2 > 0.0
    ensures median == (base1 + base2) / 2.0
{
    median := (base1 + base2) / 2.0;
}