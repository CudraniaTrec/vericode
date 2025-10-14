
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
    // Invariant: s' contains the correct transformation of the first i characters of s
    // Invariant: |s'| == i
    // Invariant: forall j :: 0 <= j < i ==> if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], s'[j]) else s'[j] == s[j]
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], s'[j]) else s'[j] == s[j]
    {
        if IsLowerCase(s[i])
        {
            assert 97 <= s[i] as int <= 122;
            assert 65 <= ShiftMinus32(s[i]) as int <= 90;
            s' := s' + [ShiftMinus32(s[i])];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    v := s';
    assert |v| == |s|;
    assert forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i];
    return s';
}

function abs(a: real) : real {if a>0.0 then a else -a}
