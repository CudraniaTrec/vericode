
predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    // Loop invariant: s' contains the correct transformation of s[0..i)
    // Loop invariant: |s'| == i
    // Loop invariant: forall j :: 0 <= j < i ==> (if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], s'[j]) else s'[j] == s[j])
    var i: int;
    i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> (if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], s'[j]) else s'[j] == s[j])
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
            assert IsLowerUpperPair(s[i], s'[i]);
        }
        else 
        {
            s' := s' + [s[i]];
            assert s'[i] == s[i];
        }
        i := i + 1;
    }
    v := s';
}

function abs(a: real) : real {if a>0.0 then a else -a}
