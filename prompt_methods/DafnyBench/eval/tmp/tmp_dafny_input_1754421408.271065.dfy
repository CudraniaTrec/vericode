
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q // Q

{
    // Strongest possible assertions for all branches

    if Valores[i] < Valores[j] {
        assert Valores[j] > Valores[i];
        if Valores[j] < Valores[k] {
            assert Valores[k] > Valores[j] > Valores[i];
            pos_padre := k ;
            pos_madre := j ;
            assert Valores[pos_padre] >= Valores[pos_madre];
            assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
        } else {
            if Valores[i] < Valores[k] {
                assert Valores[j] >= Valores[k] > Valores[i];
                pos_padre := j ;
                pos_madre := k ;
                assert Valores[pos_padre] >= Valores[pos_madre];
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
            } else {
                assert Valores[j] >= Valores[k] && Valores[i] >= Valores[k] && Valores[i] >= Valores[j];
                pos_padre := j ;
                pos_madre := i ;
                assert Valores[pos_padre] >= Valores[pos_madre];
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
            }
        }
    } else {
        assert Valores[i] >= Valores[j];
        if Valores[j] >= Valores[k] {
            assert Valores[i] >= Valores[j] >= Valores[k];
            pos_padre := i ;
            pos_madre := j ;
            assert Valores[pos_padre] >= Valores[pos_madre];
            assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
        } else {
            if Valores[i] < Valores[k] {
                assert Valores[k] > Valores[i] >= Valores[j];
                pos_padre := k ;
                pos_madre := i ;
                assert Valores[pos_padre] >= Valores[pos_madre];
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
            } else {
                assert Valores[i] >= Valores[k] > Valores[j];
                pos_padre := i ;
                pos_madre := k ;
                assert Valores[pos_padre] >= Valores[pos_madre];
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
            }
        }
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
