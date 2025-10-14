method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q // Q

{
    // Let us define the set for clarity
    var S := set x | x == i || x == j || x == k;

    if Valores[i] < Valores[j] {
        // i < j
        if Valores[j] < Valores[k] {
            // i < j < k
            pos_padre := k;
            pos_madre := j;
            assert pos_padre in S && pos_madre in S && pos_padre != pos_madre;
            assert forall r :: r in S && r != pos_padre && r != pos_madre ==> Valores[pos_padre] >= Valores[pos_madre] >= Valores[r];
        } else {
            if Valores[i] < Valores[k] {
                // i < k <= j
                pos_padre := j;
                pos_madre := k;
                assert pos_padre in S && pos_madre in S && pos_padre != pos_madre;
                assert forall r :: r in S && r != pos_padre && r != pos_madre ==> Valores[pos_padre] >= Valores[pos_madre] >= Valores[r];
            } else {
                // k <= i < j
                pos_padre := j;
                pos_madre := i;
                assert pos_padre in S && pos_madre in S && pos_padre != pos_madre;
                assert forall r :: r in S && r != pos_padre && r != pos_madre ==> Valores[pos_padre] >= Valores[pos_madre] >= Valores[r];
            }
        }
    } else {
        // i >= j
        if Valores[j] >= Valores[k] {
            // i >= j >= k
            pos_padre := i;
            pos_madre := j;
            assert pos_padre in S && pos_madre in S && pos_padre != pos_madre;
            assert forall r :: r in S && r != pos_padre && r != pos_madre ==> Valores[pos_padre] >= Valores[pos_madre] >= Valores[r];
        } else {
            if Valores[i] < Valores[k] {
                // j < i < k
                pos_padre := k;
                pos_madre := i;
                assert pos_padre in S && pos_madre in S && pos_padre != pos_madre;
                assert forall r :: r in S && r != pos_padre && r != pos_madre ==> Valores[pos_padre] >= Valores[pos_madre] >= Valores[r];
            } else {
                // j < k <= i
                pos_padre := i;
                pos_madre := k;
                assert pos_padre in S && pos_madre in S && pos_padre != pos_madre;
                assert forall r :: r in S && r != pos_padre && r != pos_madre ==> Valores[pos_padre] >= Valores[pos_madre] >= Valores[r];
            }
        }
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
