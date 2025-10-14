module Seq {
    function seq_sum(s: seq<int>) : (sum: int)
        decreases |s|
    {
        if s == [] then
            0
        else
            var x := s[0];
            var remaining := s[1..];
            x + seq_sum(remaining)
    }

    lemma SeqPartsSameSum(s: seq<int>, s1: seq<int>, s2: seq<int>)
        requires s == s1 + s2
        ensures seq_sum(s) == seq_sum(s1) + seq_sum(s2)
        decreases |s1|
    {
        if s == [] {
            // s1 and s2 must both be empty
            assert s1 == [];
            assert s2 == [];
        } else if s1 == [] {
            // s == s2
            assert s == s2;
        } else {
            // s1 != []
            var x := s1[0];
            var s1' := s1[1..];
            // s = s1 + s2 = [x] + s1' + s2 = [x] + (s1' + s2)
            assert s == [x] + (s1' + s2);
            assert s[0] == x;
            assert s[1..] == s1' + s2;
            SeqPartsSameSum(s[1..], s1[1..], s2);
            // seq_sum(s) = x + seq_sum(s[1..])
            // seq_sum(s1) = x + seq_sum(s1')
            // seq_sum(s) = x + seq_sum(s1' + s2) = x + (seq_sum(s1') + seq_sum(s2)) = (x + seq_sum(s1')) + seq_sum(s2) = seq_sum(s1) + seq_sum(s2)
        }
    }

    lemma DifferentPermutationSameSum(s1: seq<int>, s2: seq<int>)
        requires multiset(s1) == multiset(s2)
        ensures seq_sum(s1) == seq_sum(s2)
        decreases |s1|
    {
        if s1 == [] {
            assert s2 == [];
        } else {
            var x :| x in s1;
            var i1 :| 0 <= i1 < |s1| && s1[i1] == x;
            var i2 :| 0 <= i2 < |s2| && s2[i2] == x;

            var s1_left := s1[..i1];
            var s1_right := s1[i1+1..];
            var remaining1 := s1_left + s1_right;

            var s2_left := s2[..i2];
            var s2_right := s2[i2+1..];
            var remaining2 := s2_left + s2_right;

            // Prove multisets of remaining1 and remaining2 are equal
            assert multiset(remaining1) == multiset(remaining2);

            // seq_sum(s1) = seq_sum(s1_left + [x] + s1_right)
            // = seq_sum(s1_left) + x + seq_sum(s1_right)
            SeqPartsSameSum(s1, s1_left + [x], s1_right);
            SeqPartsSameSum(s1_left + [x], s1_left, [x]);
            assert seq_sum([x]) == x;

            // seq_sum(s2) = seq_sum(s2_left + [x] + s2_right)
            // = seq_sum(s2_left) + x + seq_sum(s2_right)
            SeqPartsSameSum(s2, s2_left + [x], s2_right);
            SeqPartsSameSum(s2_left + [x], s2_left, [x]);

            // Inductive step
            DifferentPermutationSameSum(remaining1, remaining2);

            // seq_sum(s1) = seq_sum(s1_left) + x + seq_sum(s1_right)
            // seq_sum(s2) = seq_sum(s2_left) + x + seq_sum(s2_right)
            // seq_sum(remaining1) = seq_sum(s1_left) + seq_sum(s1_right)
            // seq_sum(remaining2) = seq_sum(s2_left) + seq_sum(s2_right)
            // By induction, seq_sum(remaining1) == seq_sum(remaining2)
            // So seq_sum(s1) == seq_sum(s2)
        }
    }

}
function abs(a: real) : real {if a>0.0 then a else -a}
