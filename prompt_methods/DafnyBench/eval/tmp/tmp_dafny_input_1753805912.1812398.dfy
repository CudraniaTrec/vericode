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
            assert s1 == [];
            assert s2 == [];
        } else if s1 == [] {
            assert s == s2;
        } else {
            var x := s1[0];
            var s1' := s1[1..];
            assert s == [x] + s1' + s2;
            assert s[1..] == s1' + s2;
            SeqPartsSameSum(s[1..], s1[1..], s2);
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
            // Find the first occurrence of s1[0] in s2
            var i2 :| 0 <= i2 < |s2| && s2[i2] == s1[0];
            var x := s1[0];

            // Split s1 and s2 at the chosen element
            var s1_left := [];
            var s1_right := s1[1..];
            var s2_left := s2[..i2];
            var s2_right := s2[i2+1..];

            // Remove x from both sequences
            var remaining1 := s1_right;
            var remaining2 := s2_left + s2_right;

            // Prove that the multisets of the remaining sequences are equal
            assert multiset(remaining1) == multiset(s1) - multiset([x]);
            assert multiset(remaining2) == multiset(s2) - multiset([x]);
            assert multiset(remaining1) == multiset(remaining2);

            // Use the lemma for the rest
            DifferentPermutationSameSum(remaining1, remaining2);

            // Use SeqPartsSameSum to relate the sums
            // s1 = [x] + s1_right
            // s2 = s2_left + [x] + s2_right
            SeqPartsSameSum(s2, s2_left + [x], s2_right);
            SeqPartsSameSum(s2_left + [x], s2_left, [x]);
            assert seq_sum(s2_left + [x]) == seq_sum(s2_left) + seq_sum([x]);
            assert seq_sum(s2) == seq_sum(s2_left + [x]) + seq_sum(s2_right);
            assert seq_sum(s2) == seq_sum(s2_left) + seq_sum([x]) + seq_sum(s2_right);

            assert seq_sum(s1) == seq_sum([x]) + seq_sum(s1_right);
            assert seq_sum(s2) == seq_sum(s2_left) + seq_sum([x]) + seq_sum(s2_right);
            assert seq_sum(s1_right) == seq_sum(s2_left + s2_right);

            assert seq_sum(s1) == seq_sum([x]) + seq_sum(s2_left + s2_right);
            assert seq_sum(s2) == seq_sum(s2_left) + seq_sum([x]) + seq_sum(s2_right);

            // Now, seq_sum(s1) == seq_sum(s2)
        }
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
