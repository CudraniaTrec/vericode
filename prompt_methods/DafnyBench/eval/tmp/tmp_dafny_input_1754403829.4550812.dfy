
// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Monadic Laws
// Niki Vazou and Rustan Leino
// 28 March 2016

datatype List<T> = Nil | Cons(head: T, tail: List)

function append(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x, xs') => Cons(x, append(xs', ys))
}

lemma AppendNil(xs: List)
  ensures append(xs, Nil) == xs
{
  match xs
  case Nil =>
  case Cons(x, xs') =>
    AppendNil(xs');
    assert append(xs, Nil) == Cons(x, append(xs', Nil));
    assert append(xs', Nil) == xs';
    assert append(xs, Nil) == Cons(x, xs');
}

lemma AppendAssoc(xs: List, ys: List, zs: List)
  ensures append(append(xs, ys), zs) == append(xs, append(ys, zs));
{
  match xs
  case Nil =>
    assert append(append(Nil, ys), zs) == append(ys, zs);
    assert append(Nil, append(ys, zs)) == append(ys, zs);
  case Cons(x, xs') =>
    AppendAssoc(xs', ys, zs);
    assert append(append(xs, ys), zs) == Cons(x, append(append(xs', ys), zs));
    assert append(xs, append(ys, zs)) == Cons(x, append(xs', append(ys, zs)));
    assert append(append(xs', ys), zs) == append(xs', append(ys, zs));
    assert append(append(xs, ys), zs) == Cons(x, append(xs', append(ys, zs)));
    assert append(xs, append(ys, zs)) == Cons(x, append(xs', append(ys, zs)));
}

function Return<T>(a: T): List
{
  Cons(a, Nil)
}

function Bind<T,U>(xs: List<T>, f: T -> List<U>): List<U>
{
  match xs
  case Nil => Nil
  case Cons(x, xs') => append(f(x), Bind(xs', f))
}

lemma LeftIdentity<T>(a: T, f: T -> List)
  ensures Bind(Return(a), f) == f(a)
{
  AppendNil(f(a));
  assert Bind(Return(a), f) == append(f(a), Bind(Nil, f));
  assert Bind(Nil, f) == Nil;
  assert append(f(a), Nil) == f(a);
}

lemma RightIdentity<T>(m: List)
  ensures Bind(m, Return) == m
{
  match m
  case Nil =>
    assert Bind(Nil, Return) == Nil;
  case Cons(x, m') =>
    RightIdentity(m');
    assert Bind(Cons(x, m'), Return) == append(Return(x), Bind(m', Return));
    assert Bind(m', Return) == m';
    assert append(Return(x), m') == Cons(x, m');
    assert Bind(Cons(x, m'), Return) == Cons(x, m');
    calc {
      Bind(Cons(x, m'), Return);
      append(Return(x), Bind(m', Return));
      Cons(x, Bind(m', Return));
      Cons(x, m');
    }
}

lemma Associativity<T>(m: List, f: T -> List, g: T -> List)
  ensures Bind(Bind(m, f), g) == Bind(m, x => Bind(f(x), g))
{
  match m
  case Nil =>
    assert Bind(Bind(Nil, f), g) == Bind(Nil, x => Bind(f(x), g));
    assert Bind(Nil, f) == Nil;
    assert Bind(Nil, g) == Nil;
    assert Bind(Nil, x => Bind(f(x), g)) == Nil;
  case Cons(x, xs) =>
    Associativity(xs, f, g);
    match f(x)
    case Nil =>
      assert Bind(f(x), g) == Nil;
      assert append(Bind(f(x), g), Bind(xs, y => Bind(f(y), g))) == Bind(xs, y => Bind(f(y), g));
      assert Bind(Cons(x, xs), y => Bind(f(y), g)) == append(Bind(f(x), g), Bind(xs, y => Bind(f(y), g)));
      calc {
        Bind(xs, y => Bind(f(y), g));
        Bind(Cons(x, xs), y => Bind(f(y), g));
      }
    case Cons(y, ys) =>
      BindOverAppend(ys, Bind(xs, f), g);
      Associativity(xs, f, g);
      AppendAssoc(g(y), Bind(ys, g), Bind(Bind(xs, f), g));
      assert Bind(f(x), g) == append(g(y), Bind(ys, g));
      assert Bind(xs, f) == Bind(xs, f);
      assert Bind(append(ys, Bind(xs, f)), g) == append(Bind(ys, g), Bind(Bind(xs, f), g));
      assert append(g(y), Bind(append(ys, Bind(xs, f)), g)) == append(g(y), append(Bind(ys, g), Bind(Bind(xs, f), g)));
      assert append(g(y), append(Bind(ys, g), Bind(Bind(xs, f), g))) == append(append(g(y), Bind(ys, g)), Bind(Bind(xs, f), g));
      assert append(append(g(y), Bind(ys, g)), Bind(Bind(xs, f), g)) == Bind(Cons(x, xs), z => Bind(f(z), g));
      calc {
        append(g(y), Bind(append(ys, Bind(xs, f)), g));
        { BindOverAppend(ys, Bind(xs, f), g); }
        append(g(y), append(Bind(ys, g), Bind(Bind(xs, f), g)));
        { AppendAssoc(g(y), Bind(ys, g), Bind(Bind(xs, f), g)); }
        append(append(g(y), Bind(ys, g)), Bind(Bind(xs, f), g));
        Bind(Cons(x, xs), z => Bind(f(z), g));
      }
}

lemma BindOverAppend<T>(xs: List, ys: List, g: T -> List)
  ensures Bind(append(xs, ys), g) == append(Bind(xs, g), Bind(ys, g))
{
  match xs
  case Nil =>
    assert append(Nil, ys) == ys;
    assert Bind(ys, g) == Bind(ys, g);
    assert Bind(append(Nil, ys), g) == Bind(ys, g);
    assert append(Bind(Nil, g), Bind(ys, g)) == append(Nil, Bind(ys, g));
    assert append(Nil, Bind(ys, g)) == Bind(ys, g);
  case Cons(x, xs') =>
    BindOverAppend(xs', ys, g);
    AppendAssoc(g(x), Bind(xs', g), Bind(ys, g));
    assert append(xs, ys) == Cons(x, append(xs', ys));
    assert Bind(append(xs, ys), g) == append(g(x), Bind(append(xs', ys), g));
    assert append(Bind(xs, g), Bind(ys, g)) == append(append(g(x), Bind(xs', g)), Bind(ys, g));
    assert append(g(x), append(Bind(xs', g), Bind(ys, g))) == append(append(g(x), Bind(xs', g)), Bind(ys, g));
    assert append(g(x), Bind(append(xs', ys), g)) == append(g(x), append(Bind(xs', g), Bind(ys, g)));
}

function abs(a: real) : real {if a>0.0 then a else -a}
