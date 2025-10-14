// Forall
method Q1(){
    var a := new int[6];
    a[0], a[1], a[2], a[3], a[4], a[5] := 1,0,0,0,1,1;
    var b := new int[3];
    b[0], b[1], b[2] := 1, 0, 1;

    var j,k := 1,3;
    var p,r := 4,5;

    // a) All elements in the range a[j..k] == 0
    // j=1, k=3, so a[1], a[2], a[3] == 0
    assert a[1] == 0 && a[2] == 0 && a[3] == 0;

    // b) All zeros in a occur in the interval a[j..k]
    // All zeros are at indices 1,2,3, which are in [1,3]
    assert (forall i :: 0 <= i < a.Length && a[i] == 0 ==> 1 <= i <= 3);

    // c) It is *not* the case that all ones of a occur in the interval in a[p..r]
    // p=4, r=5, so a[4], a[5] == 1, but a[0] == 1 as well, which is not in [4,5]
    assert a[0] == 1 && (0 < 4 || 0 > 5);

    // d) a[0..n-1] contains at least two zeros
    // There are three zeros at indices 1,2,3
    assert (a[1] == 0 && a[2] == 0) || (a[1] == 0 && a[3] == 0) || (a[2] == 0 && a[3] == 0);

    // e) b[0..n-1] contains at the most two zeros (Note: *not* true for array a)
    // b[1] == 0, only one zero
    assert (b[0] == 0 as bool then 1 else 0) + (b[1] == 0 as bool then 1 else 0) + (b[2] == 0 as bool then 1 else 0) <= 2;
}

// Quantifiers
class Secret{
    var secret : int;
    var known : bool;
    var count : int;

    method Init(x : int)
    modifies `secret, `known, `count
    requires 1 <= x <= 10
    ensures secret == x
    ensures known == false
    ensures count == 0
    {
        known := false;
        count := 0;
        secret := x;
    }

    method Guess(g : int) returns (result : bool, guesses : int)
    modifies `known, `count
    requires known == false
    ensures if g == secret then 
                result == true && known == true 
            else 
                result == false && known == false
    ensures count == old(count) + 1 && guesses == count
    {
        if (g == secret)
        {
            known := true;
            result := true;
        }
        else
        {
            result := false;
        }
        count := count + 1;
        guesses := count;
    }

    method Main()
    {
        var testObject : Secret := new Secret.Init(5);
        var x, y := testObject.Guess(0);

        x,y := testObject.Guess(5);

        //x,y := testObject.Guess(5);

    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
