def f(x: {x: Nat, x < 5}) = { x }

def g(x: Nat) = {
  if(true) {
    val y: {x: Nat, x < 5} = 0 in
    y
  }
  else {
    val y: {x: Nat, x > 5} = 10 in
    y
  }
}

val z = f (g 2) in

def h(x: Nat) = {
  match Left(2) {
    case Left(x) =>
      val y: {x: Nat, x < 5} = 0 in
      y
    case Right(x) =>
      val y: {x: Nat, x > 5} = 10 in
      y
  }
}

f (g 2)
