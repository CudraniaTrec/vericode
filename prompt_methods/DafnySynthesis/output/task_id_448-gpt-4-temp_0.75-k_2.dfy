//Dafny Code

method SumPerrinNumbers(n: nat) returns (sum: nat)
    requires n >= 0
    ensures sum == (if n == 0 then 3
                    else if n == 1 then 4
                    else if n == 2 then 2
                    else var s := 0; var a := 3; var b := 4; var c := 2;
                         forall i :: 3 <= i <= n ==> 
                            var perrin := if i == 0 then a else if i == 1 then b else if i == 2 then c else 0;
                         s == a + b + c + sum (i: 3 .. n) (Perrin(i))
                   )
{
    if n == 0 {
        sum := 3;
    } else if n == 1 {
        sum := 3 + 4;
    } else if n == 2 {
        sum := 3 + 4 + 2;
    } else {
        var a := 3;
        var b := 4;
        var c := 2;
        sum := a + b + c;
        var i := 3;
        while i <= n
            invariant 3 <= i <= n+1
            invariant sum == a + b + c + (if i > 3 then (sum (j: 3 .. i-1) (Perrin(j))) else 0)
            decreases n - i + 1
        {
            var d := a + b;
            sum := sum + d;
            a := b;
            b := c;
            c := d;
            i := i + 1;
        }
    }
}