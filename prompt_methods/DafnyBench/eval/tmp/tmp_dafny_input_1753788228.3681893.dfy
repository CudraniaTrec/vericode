// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate p(i:int)

method m1()

method m2()
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
    {
        assume exists i :: p(i);
        // strongest annotation: arr.Length > 0 always holds here
        assert arr.Length > 0;
        arr[0] := 1;
        // strongest annotation: arr[0] == 1 after assignment
        assert arr[0] == 1;
    }
}
function abs(a: real) : real {if a>0.0 then a else -a}
