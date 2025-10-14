method FactorialOfLastDigit(n: int) returns (fact: int)
    requires n >= 0
    ensures 0 <= n ==> fact == if n == 0 then 1 else 
        var d := n % 10;
        if d == 0 then 1
        else if d == 1 then 1
        else if d == 2 then 2
        else if d == 3 then 6
        else if d == 4 then 24
        else if d == 5 then 120
        else if d == 6 then 720
        else if d == 7 then 5040
        else if d == 8 then 40320
        else 362880
{
    var d := n % 10;
    if d == 0 || d == 1 {
        fact := 1;
    } else if d == 2 {
        fact := 2;
    } else if d == 3 {
        fact := 6;
    } else if d == 4 {
        fact := 24;
    } else if d == 5 {
        fact := 120;
    } else if d == 6 {
        fact := 720;
    } else if d == 7 {
        fact := 5040;
    } else if d == 8 {
        fact := 40320;
    } else {
        // d == 9
        fact := 362880;
    }
}