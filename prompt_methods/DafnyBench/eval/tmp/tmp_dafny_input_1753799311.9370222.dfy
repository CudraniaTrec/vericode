
// Exemplo de invariantes
// Invariante significa que o valor não muda desde a pré-condição até a pós-condição

method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    // parâmetros de entrada são imutáveis, por isso
    // é preciso a atribuir a variáveis locais para usar em blocos de códigos para mudar

    var m := x;
    var n := y;

    r := 0;
    while m > 0 
        invariant 0 <= m <= x
        invariant n == y
        invariant r + m * n == x * y
    {
        r := r + n;
        m := m -1;
    }
    assert m == 0;
    assert r == x * y;
    return r;
}

// Teste do método para encontrar a invariante
// x | y | m | n | r
// 5 | 3 | 5 | 3 | 0
// 5 | 3 | 4 | 3 | 3
// 5 | 3 | 3 | 3 | 6
// 5 | 3 | 2 | 3 | 9
// 5 | 3 | 1 | 3 | 12
// 5 | 3 | 0 | 3 | 15

// vimos o seguinte:
// m * n + r = x * y
// 5 * 3 + 0 (15) = 5 * 3 (15)
// portanto a fórmula m*n+r == x*y é uma invariante
// mas só isso não serve, o m ele é maior ou igual a zero quando acaba o while
// por isso, também é a invariante que necessita
// com isso dizemos para o programa as alterações do m de maior ou igual a zero
// e mostramos a função encontrada que alterava o valor de m e n das variaveis criadas

// SE OS ALGORITMOS TIVEREM REPETIÇÃO OU RECURSÃO, DEVEM SER MOSTRADOS QUAIS SÃO AS INVARIANTES
// OU SEJA, OS VALORES QUE NÃO ESTÃO SENDO MUDADOS E COLOCAR A FÓRMULA DELE COMO ACIMA

function abs(a: real) : real {if a>0.0 then a else -a}
