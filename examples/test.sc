def f(x: Nat): Nat = {
  if(x > 2) { x - 2} else { x + 2 }
}

def g(x: Nat + Nat): Nat = {
  match x {
    case Left(x) => x
    case Right(x) => x
  }
}

val x = 2 in
val y = 4 in
val z = (1, 2) in
f(x + y + First(z) + f(f(2)))