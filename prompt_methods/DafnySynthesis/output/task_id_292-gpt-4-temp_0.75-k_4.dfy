method Quotient(a: int, b: int) returns (q: int)
    requires b != 0
    ensures a == q * b + r && 0 <= r < |b| // Division algorithm
    ensures q == a / b
{
    q := a / b;
}