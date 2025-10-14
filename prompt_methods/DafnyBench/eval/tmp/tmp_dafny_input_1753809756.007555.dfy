method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q // Q

{
    // All indices are distinct and within bounds by precondition

    // There are 6 possible orderings for 3 elements; we cover all

    if Valores[i] < Valores[j] {
        // i < j
        if Valores[j] < Valores[k] {
            // i < j < k
            pos_padre := k ;
            pos_madre := j ;
            // k > j > i
            // k: max, j: mid, i: min
            assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
            assert Valores[pos_padre] >= Valores[pos_madre];
        } else {
            if Valores[i] < Valores[k] {
                // i < k <= j
                pos_padre := j ;
                pos_madre := k ;
                // j: max, k: mid, i: min
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
                assert Valores[pos_padre] >= Valores[pos_madre];
            } else {
                // k <= i < j
                pos_padre := j ;
                pos_madre := i ;
                // j: max, i: mid, k: min
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
                assert Valores[pos_padre] >= Valores[pos_madre];
            }
        }
    } else {
        // i >= j
        if Valores[j] >= Valores[k] {
            // i >= j >= k
            pos_padre := i ;
            pos_madre := j ;
            // i: max, j: mid, k: min
            assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
            assert Valores[pos_padre] >= Valores[pos_madre];
        } else {
            if Valores[i] < Valores[k] {
                // j < i < k
                pos_padre := k ;
                pos_madre := i ;
                // k: max, i: mid, j: min
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
                assert Valores[pos_padre] >= Valores[pos_madre];
            } else {
                // j < k <= i
                pos_padre := i ;
                pos_madre := k ;
                // i: max, k: mid, j: min
                assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre;
                assert Valores[pos_padre] >= Valores[pos_madre];
            }
        }
    }

    // Prove the ensures clause by explicit witness
    // The third index (not pos_padre or pos_madre) is:
    var all := [i, j, k];
    var used := [pos_padre, pos_madre];
    var idx := if all[0] != used[0] && all[0] != used[1] then all[0]
               else if all[1] != used[0] && all[1] != used[1] then all[1]
               else all[2];
    assert idx in {i, j, k} && idx != pos_padre && idx != pos_madre;
    assert Valores[pos_padre] >= Valores[pos_madre] && (
        (Valores[pos_madre] >= Valores[idx]) || (Valores[pos_padre] >= Valores[idx])
    );
    // Strongest assertion: pos_padre, pos_madre, idx are a permutation of i, j, k
}

function abs(a: real) : real {if a>0.0 then a else -a}
