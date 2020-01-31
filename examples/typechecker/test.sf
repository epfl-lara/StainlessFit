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

fun badDef( x [{x [Nat] | x < second (fix[n => Nat](div => div), 2) }] )
  [returns Nat] = {
  2
}


fun ff (x [{x [Nat] | false}]) = { x }

fun gg (x [{x [Nat] | false}]) = { ff x }

fun hh (x [{x [Nat] | true || false}]) = { 2 }

val two = hh 2;

val q [Nat] = h();
val x [Nat] = 2;
val y [Nat]  = 4;
val z [Sigma(x: Nat, Nat)] = (1, 2);

f(x + y + first z + f (f 2)) + g(left 22) / g(right 22)
