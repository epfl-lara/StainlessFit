Include("../assert.sc")

fun f(x [Nat])  [returns Nat] = {
  if (x > 2) { x - 2} else { x + 2 }
}

fun g(x [Nat + Nat])  [returns Nat] = {
  match x {
    case left(x) => x
    case right(x) => x
  }
}

fun h(x [Unit]) = {
  2
}

val fact = fix[n => Nat => Nat](fac =>
  fun of (m [Nat]) = {
      if (m == 0) { 1 }
      else { m * (fac (m - 1)) }
  }
);
val q [Nat] = h();
val x [Nat] = 2;
val y [Nat] = 4;
val z [(Nat, Nat)] = (1, 2);
val p [Nat] = f(x + y + first z + f(f(2))) + g(left 22) / g(right 22);
assert(p == 8)
