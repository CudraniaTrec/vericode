
/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of a real number (x^n), 
* illustrating the usage of lemmas and automatic induction in Dafny.
* J.  Pascoal Faria, FEUP, Jan/2022.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
function power(x: real, n: nat) : real {
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Computation of x^n in time and space O(log n).
method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{
    if n == 0 {
        assert power(x, 0) == 1.0;
        return 1.0;
    }
    else if n == 1 {
        assert power(x, 1) == x;
        return x;
    }
    else if n % 2 == 0 {
        // n even, n = 2k
        assert n/2 + n/2 == n;
        productOfPowers(x,  n/2, n/2); // recall lemma
        var temp := powerDC(x, n/2);
        assert temp == power(x, n/2);
        assert temp * temp == power(x, n/2) * power(x, n/2);
        assert temp * temp == power(x, n);
        return temp * temp;
    }
    else {
        // n odd, n = 2k+1
        assert (n-1)/2 + (n-1)/2 == n-1;
        productOfPowers(x, (n-1)/2, (n-1)/2); // recall lemma  
        var temp := powerDC(x, (n-1)/2);
        assert temp == power(x, (n-1)/2);
        assert temp * temp == power(x, (n-1)/2) * power(x, (n-1)/2);
        assert temp * temp == power(x, n-1);
        assert temp * temp * x == power(x, n-1) * x;
        assert temp * temp * x == power(x, n);
        return temp * temp * x;
    } 
}

// States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
// The property is proved by automatic induction on 'a'.
lemma {:induction a} productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
    if a == 0 {
        // power(x, 0) * power(x, b) == 1.0 * power(x, b) == power(x, b) == power(x, 0 + b)
        assert power(x, 0) == 1.0;
        assert power(x, 0) * power(x, b) == power(x, b);
        assert power(x, 0 + b) == power(x, b);
    } else {
        // Inductive case: a > 0
        // power(x, a) * power(x, b) == x * power(x, a-1) * power(x, b)
        // == x * (power(x, a-1) * power(x, b)) == x * power(x, (a-1)+b) [by IH]
        // == power(x, 1 + (a-1) + b) == power(x, a + b)
        productOfPowers(x, a-1, b);
        assert power(x, a) == x * power(x, a-1);
        assert power(x, a) * power(x, b) == x * power(x, a-1) * power(x, b);
        assert x * (power(x, a-1) * power(x, b)) == x * power(x, (a-1) + b);
        assert x * power(x, (a-1) + b) == power(x, 1 + (a-1) + b);
        assert 1 + (a-1) + b == a + b;
        assert power(x, 1 + (a-1) + b) == power(x, a + b);
    }
}


// A few test cases (checked statically by Dafny).
method testPowerDC() {
    var p1 := powerDC( 2.0, 5); assert p1 == 32.0;
    var p2 := powerDC(-2.0, 2); assert p2 == 4.0;
    var p3 := powerDC(-2.0, 1); assert p3 == -2.0;
    var p4 := powerDC(-2.0, 0); assert p4 == 1.0;
    var p5 := powerDC( 0.0, 0); assert p5 == 1.0;
}

function abs(a: real) : real {if a>0.0 then a else -a}
