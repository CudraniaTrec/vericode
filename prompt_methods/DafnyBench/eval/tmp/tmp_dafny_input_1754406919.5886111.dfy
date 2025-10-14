
method SumOfDigits(number: nat) returns (sum: nat)
  requires number >= 0
  ensures sum >= 0
  ensures sum == SumDigits(number)
{
  sum := 0;
  var n: nat := number;

  // Let's find out the number of digits, which is the same as powers of ten for the given number
  ghost var ndigits := NumberOfDigits(number);
  X(number);

  ghost var PowersOfTen := seq(ndigits+1, i requires 0 <= i <= ndigits => Power10(i));
  ghost var pmax := Power10(ndigits);
  ghost var p := PowersOfTen[0];

  // Let's compute the values of n
  ghost var ValuesOfn := seq(ndigits+1, i requires 0 <= i <= ndigits => number / PowersOfTen[i]);
  //DivIsZero();

  ghost var i := 0;
  while n > 0
    invariant 0 <= n <= number
    invariant sum == SumDigits(number) - SumDigits(n)
    invariant i <= ndigits
    invariant p == Power10(i)
    invariant forall j :: 0 <= j < i ==> ((number / Power10(j)) % 10) == ((number / Power10(j)) % 10)
    invariant n == if i == ndigits then 0 else number / Power10(i)
    invariant sum >= 0
  {
    var digit := n % 10;
    sum := sum + digit;
    n := n / 10;
    i := i + 1;
    p := PowersOfTen[i]; //p * 10;
    assert sum == SumDigits(number) - SumDigits(n);
  }
  assert n == 0;
  assert sum == SumDigits(number);
  NumberIdentity(number, p);
}

function abs(a: real) : real {if a>0.0 then a else -a}
