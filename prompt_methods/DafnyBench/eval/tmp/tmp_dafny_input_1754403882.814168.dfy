// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Monadic Laws
// Niki Vazou and Rustan Leino
// 28 March 2016

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
  case Nil => ys
  case Cons(x, xs') => Cons(x, append(xs', ys))
}

lemma AppendNil<T>(xs: List<T>)
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

lemma AppendAssoc<T>(xs: List<T>, ys: List<T>, zs: List<T>)
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

function Return<T>(a: T): List<T>
{
  Cons(a, Nil)
}

function Bind<T,U>(xs: List<T>, f: T -> List<U>): List<U>
{
  match xs
  case Nil => Nil
  case Cons(x, xs') => append(f(x), Bind(xs', f))
}

lemma LeftIdentity<T>(a: T, f: T -> List<T>)
  ensures Bind(Return<T>(a), f) == f(a)
{
  AppendNil<T>(f(a));
  assert Bind(Return<T>(a), f) == append(f(a), Bind(Nil, f));
  assert Bind(Nil, f) == Nil;
  assert append(f(a), Nil) == f(a);
}

lemma RightIdentity<T>(m: List<T>)
  ensures Bind(m, Return<T>) == m
{
  match m
  case Nil =>
    assert Bind(Nil, Return<T>) == Nil;
  case Cons(x, m') =>
    RightIdentity(m');
    assert Bind(Cons(x, m'), Return<T>) == append(Return<T>(x), Bind(m', Return<T>));
    assert Bind(m', Return<T>) == m';
    assert append(Return<T>(x), m') == Cons(x, m');
    assert Bind(Cons(x, m'), Return<T>) == Cons(x, m');
}

lemma Associativity<T>(m: List<T>, f: T -> List<T>, g: T -> List<T>)
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
    case Cons(y, ys) =>
      BindOverAppend<T>(ys, Bind(xs, f), g);
      Associativity(xs, f, g);
      AppendAssoc<T>(g(y), Bind(ys, g), Bind(Bind(xs, f), g));
      assert Bind(f(x), g) == append(g(y), Bind(ys, g));
      assert Bind(xs, f) == Bind(xs, f);
      assert Bind(append(ys, Bind(xs, f)), g) == append(Bind(ys, g), Bind(Bind(xs, f), g));
      assert append(g(y), Bind(append(ys, Bind(xs, f)), g)) == append(g(y), append(Bind(ys, g), Bind(Bind(xs, f), g)));
      assert append(g(y), append(Bind(ys, g), Bind(Bind(xs, f), g))) == append(append(g(y), Bind(ys, g)), Bind(Bind(xs, f), g));
      assert append(append(g(y), Bind(ys, g)), Bind(Bind(xs, f), g)) == Bind(Cons(x, xs), z => Bind(f(z), g));
}

lemma BindOverAppend<T>(xs: List<T>, ys: List<T>, g: T -> List<T>)
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
    AppendAssoc<T>(g(x), Bind(xs', g), Bind(ys, g));
    assert append(xs, ys) == Cons(x, append(xs', ys));
    assert Bind(append(xs, ys), g) == append(g(x), Bind(append(xs', ys), g));
    assert append(Bind(xs, g), Bind(ys, g)) == append(append(g(x), Bind(xs', g)), Bind(ys, g));
    assert append(g(x), append(Bind(xs', g), Bind(ys, g))) == append(append(g(x), Bind(xs', g)), Bind(ys, g));
    assert append(g(x), Bind(append(xs', ys), g)) == append(g(x), append(Bind(xs', g), Bind(ys, g)));
}

function abs(a: real) : real {if a>0.0 then a else -a}
