method Quotient(a: int, b: int) returns (q: int)
    requires b != 0 // Division by zero is not allowed
    ensures a == b * q + (a % b)
    ensures 0 <= if b > 0 then a - b * q < b else b < a - b * q <= 0
{
    // The quotient rounded down to the nearest integer is just a / b in Dafny
    q := a / b;
}