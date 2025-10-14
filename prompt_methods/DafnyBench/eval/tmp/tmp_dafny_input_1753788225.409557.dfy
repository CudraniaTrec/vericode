
// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate p(i:int)

method m1()
    ensures exists i :: p(i);

method m2()
    ensures exists i :: p(i)
{
  assume exists i :: p(i);
  m1();
}

class Test
{
    var arr : array<int>;
    predicate p(i: int)
    method foo()
        requires arr.Length > 0
        modifies arr
        ensures arr[0] == 1
    {
        assume exists i :: p(i);
        arr[0] := 1;
        assert arr[0] == 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
