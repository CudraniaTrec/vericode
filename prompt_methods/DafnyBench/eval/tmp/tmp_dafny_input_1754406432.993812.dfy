
function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}

method CountTrue(a: array<bool>) returns (result: int)
    requires a != null
    ensures result == countTo(a, a.Length)
{
    result := 0;
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result == countTo(a, i)
        invariant a != null
    {
        if a[i] {
            result := result + 1;
        }
        i := i + 1;
    }
}

function abs(a: real) : real {if a>0.0 then a else -a}
