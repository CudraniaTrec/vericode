
method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{
    var a := n / 100;
    var b := (n / 10) % 10;
    var c := n % 10;

    assert 0 <= a < 10;
    assert 0 <= b < 10;
    assert 0 <= c < 10;
    assert n == a * 100 + b * 10 + c;

    result := n == (a * a * a + b * b * b + c * c * c);

    assert result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)));
}

function abs(a: real) : real {if a>0.0 then a else -a}
