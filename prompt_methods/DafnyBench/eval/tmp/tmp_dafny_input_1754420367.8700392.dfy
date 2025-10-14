
class Contador
{
    var valor: int;

    //construtor anônimo
    constructor ()
      ensures valor == 0
    {
        valor := 0;
        assert valor == 0;
    }

    //construtor com nome
    constructor Init(v:int)
      ensures valor == v
    {
        valor := v;
        assert valor == v;
    }

    method Incrementa()
      modifies this
      ensures valor == old(valor) + 1
    {
        var oldValor := valor;
        valor := valor + 1;
        assert valor == oldValor + 1;
    }

    method Decrementa()
      modifies this
      ensures valor == old(valor) - 1
    {
        var oldValor := valor;
        valor := valor -1 ;
        assert valor == oldValor - 1;
    }

    method GetValor() returns (v:int)
      ensures v == valor
    {
        v := valor;
        assert v == valor;
        return v;
    }
}

method Main()
{
    var c := new Contador(); //cria um novo objeto no heap via construtor anônimo
    assert c.valor == 0;
    var c2 := new Contador.Init(10); //cria um novo objeto no heap via construtor nomeado
    assert c2.valor == 10;
    var v := c.GetValor();
    assert v == c.valor;
    var v2 := c2.GetValor();
    assert v2 == c2.valor;
    c.Incrementa();
    assert c.valor == 1;
    v := c.GetValor();
    assert v == c.valor;
    c.Decrementa();
    assert c.valor == 0;
    v := c.GetValor();
    assert v == c.valor;
}

function abs(a: real) : real {if a>0.0 then a else -a}
