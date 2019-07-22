def f(x: Nat): Nat = {
  if(x > 2) { x - 2} else { x + 2 }
}

def g(x: Nat + Nat): Nat = {
  match x {
    case Left(x) => x
    case Right(x) => x
  }
}

val x: Nat = 2 in
val y: Nat  = 4 in
val z: (Nat, Nat) = (1, 2) in
val p: Nat = f(x + y + First(z) + f(f(2))) + g(Left(22)) / g(Right(22)) in
g(Left(22))

// Should returns 7
