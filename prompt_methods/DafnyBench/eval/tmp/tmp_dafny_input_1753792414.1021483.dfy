
predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    var i: int := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant |s'| == i
        invariant forall j :: 0 <= j < i ==> 
            if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], s'[j]) 
            else if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], s'[j]) 
            else s'[j] == s[j]
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
            assert IsLowerUpperPair(s[i], s'[i]);
        }
        else if IsUpperCase(s[i])
        {
            s' := s' + [Shift32(s[i])];
            assert IsUpperLowerPair(s[i], s'[i]);
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
