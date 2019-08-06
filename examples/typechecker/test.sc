def f(x: Nat): Nat = {
  if(x > 2) { x - 2} else { x + 2 }
}

def g(x: Nat + Nat): Nat = {
  match x {
    case Left(x) => x
    case Right(x) => x
  }
}

def h() = {
  2
}

val q: Nat = h() in
val x: Nat = 2 in
val y: Nat  = 4 in
val z: (Nat, Nat) = (1, 2) in
f(x + y + First(z) + f(f(2))) + g(Left(22)) / g(Right(22))
