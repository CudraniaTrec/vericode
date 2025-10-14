
// Ejercicio 1: Demostrar por inducción el siguiente lema:

lemma EcCuadDiv2_Lemma (x:int)
    requires x >= 1 
    ensures (x*x + x) % 2 == 0
{
    if x != 1 { 
        EcCuadDiv2_Lemma(x-1);
        // (x*x + x) = ((x-1)*(x-1) + (x-1)) + 2*x
        // Both (x-1)*(x-1) + (x-1) and 2*x are even, so their sum is even
        assert ((x-1)*(x-1) + (x-1)) % 2 == 0;
        assert (2*x) % 2 == 0;
        assert (x*x + x) == ((x-1)*(x-1) + (x-1)) + 2*x;
        assert ((x*x + x) % 2) == (((x-1)*(x-1) + (x-1)) % 2 + (2*x) % 2) % 2;
        assert ((x*x + x) % 2) == (0 + 0) % 2;
        assert (x*x + x) % 2 == 0;
    } else {
        assert (1*1 + 1) % 2 == 2 % 2 == 0;
    }
}


// Ejercicio 2: Demostrar por inducción el siguiente lema
// Indicaciones: (1) Puedes llamar al lema del ejercicio anterior, si lo necesitas.
//               (2) Recuerda que, a veces, simplificar la HI puede ayudar a saber donde utilizarla.

lemma EcCubicaDiv6_Lemma (x:int)
    requires x >= 1
    ensures (x*x*x + 3*x*x + 2*x) % 6 == 0
{
    if x > 1 {
        EcCubicaDiv6_Lemma(x-1);
        EcCuadDiv2_Lemma(x);
        // (x^3 + 3x^2 + 2x) - ((x-1)^3 + 3(x-1)^2 + 2(x-1)) = 
        // [x^3 - (x-1)^3] + 3[x^2 - (x-1)^2] + 2[x - (x-1)]
        // = (3x^2 - 3x + 1) + 3(2x - 1) + 2
        // = 3x^2 - 3x + 1 + 6x - 3 + 2
        // = 3x^2 + 3x + 0
        // = 3x(x+1)
        // 3x(x+1) is always divisible by 6 since x(x+1) is always even
        assert ((x*x + x) % 2 == 0); // by EcCuadDiv2_Lemma(x)
        assert ((x*x*x + 3*x*x + 2*x) - ((x-1)*(x-1)*(x-1) + 3*(x-1)*(x-1) + 2*(x-1))) == 3*x*(x+1);
        assert (3*x*(x+1)) % 6 == 0;
        // Therefore, if the previous value is divisible by 6, so is the current
    } else {
        assert (1*1*1 + 3*1*1 + 2*1) % 6 == (1 + 3 + 2) % 6 == 6 % 6 == 0;
    }
}

// Ejercicio 3: Probar por contradicción el siguiente lemma:

lemma cubEven_Lemma (x:int)
    requires (x*x*x + 5) % 2 == 1
    ensures x % 2 == 0
{
    if x % 2 == 1 {
        var k := (x-1)/2;
        // x = 2k+1, so x^3 + 5 = (2k+1)^3 + 5 = 8k^3 + 12k^2 + 6k + 1 + 5 = 8k^3 + 12k^2 + 6k + 6
        // = 2*(4k^3 + 6k^2 + 3k + 3), which is even, so (x^3 + 5) % 2 == 0, contradiction.
        assert x == 2*k + 1;
        assert x*x*x + 5 == 8*k*k*k + 12*k*k + 6*k + 6;
        assert (x*x*x + 5) % 2 == 0;
        assert false;
    } else {
        assert x % 2 == 0;
    }
}

// Ejercicio 4:  Prueba el siguiente lemma por casos (de acuerdo a los tres valores posibles de x%3)
lemma perfectCube_Lemma (x:int)
    ensures exists z :: (x*x*x == 3*z || x*x*x == 3*z + 1 || x*x*x == 3*z - 1);
{
    if x%3 == 0 {
        var k := x/3;
        // x = 3k, x^3 = 27k^3 = 3*(9k^3)
        assert x == 3*k;
        assert x*x*x == 3*(9*k*k*k);
        assert exists z :: x*x*x == 3*z;
    }
    else if x%3 == 1 {
        var k := (x-1)/3;
        // x = 3k+1, x^3 = (3k+1)^3 = 27k^3 + 27k^2 + 9k + 1 = 3*(9k^3 + 9k^2 + 3k) + 1
        assert x == 3*k + 1;
        assert x*x*x == 3*(9*k*k*k + 9*k*k + 3*k) + 1;
        assert exists z :: x*x*x == 3*z + 1;
    }
    else {
        var k := (x-2)/3;
        // x = 3k+2, x^3 = (3k+2)^3 = 27k^3 + 54k^2 + 36k + 8 = 3*(9k^3 + 18k^2 + 12k) + 8
        // 8 = 3*2 + 2, so x^3 = 3*(9k^3 + 18k^2 + 12k + 2) + 2
        // 2 = -1 mod 3, so x^3 = 3z - 1 for some z
        assert x == 3*k + 2;
        assert x*x*x == 3*(9*k*k*k + 18*k*k + 12*k + 2) + 2;
        assert exists z :: x*x*x == 3*z - 1;
    }
}

// Ejercicio 5: Dada la siguiente función exp y los dos lemmas expGET1_Lemma y prodMon_Lemma (que Dafny demuestra automáticamente)
// demostrar el lemma expMon_Lemma por inducción en n. Usar calc {} y poner como "hints" las llamadas a los lemmas en los 
// pasos del cálculo donde son utilizadas.

function exp(x:int, e:nat):int
{
    if e == 0 then 1 else x * exp(x,e-1)
}

lemma expGET1_Lemma(x:int, e:nat)			
    requires x >= 1 
    ensures exp(x,e) >= 1
{}

lemma prodMon_Lemma(z:int, a:int, b:int)
    requires z >= 1 && a >= b >= 1
    ensures  z*a >= z*b
{}

lemma expMon_Lemma(x:int, n:nat)
	requires x >= 1 && n >= 1
	ensures exp(x+1,n) >= exp(x,n) + 1 
{
    if n != 1 { 
        calc {
            exp(x+1,n);
            ==
            (x+1)*exp(x+1,n-1);
            ==
            x*exp(x+1,n-1) + exp(x+1,n-1);
            >= {
                expGET1_Lemma(x+1,n-1);
            }
            x*exp(x+1,n-1) + 1;
            >= {
                expMon_Lemma(x,n-1);
                // exp(x+1,n-1) >= exp(x,n-1) + 1
                prodMon_Lemma(x, exp(x+1,n-1), exp(x,n-1) + 1);
                // x*exp(x+1,n-1) >= x*(exp(x,n-1) + 1)
            }
            x*(exp(x,n-1) + 1) + 1;
            ==
            x*exp(x,n-1) + x + 1;
            ==
            (x*exp(x,n-1) + x) + 1;
            ==
            exp(x,n) + 1;
        }
    } else {
        // n == 1
        assert exp(x+1,1) == x+1;
        assert exp(x,1) == x;
        assert exp(x+1,1) >= exp(x,1) + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
