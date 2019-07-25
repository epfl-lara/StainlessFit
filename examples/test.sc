def f(x: Nat): Nat = {
  if(x > 2) { x - 2} else { x + 2 }
}

def g(x: Nat + Nat): Nat = {
  match x {
    case Left(x) => x
    case Right(x) => x
  }
}

val fact = fix[n => Nat => Nat](fac =>
  fun (m: Nat) => {
      if(m == 0) 1
      else m * (fac (m - 1))
  }
) in
val x: Nat = 2 in
val y: Nat  = 4 in
val z: (Nat, Nat) = (1, 2) in
val p: Nat = f(x + y + First(z) + f(f(2))) + g(Left(22)) / g(Right(22)) in
assert(p == 8)

//Should returns 8
