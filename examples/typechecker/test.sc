def f(x: Nat): Nat = {
  if(x > 2) { x - 2} else { x + 2 }
}

def g(x: Nat + Nat): Nat = {
  match x {
    case Left(x) => x
    case Right(x) => x
  }
}

def h(x: Unit) = {
  2
}

def badDef(x: {x: Nat, x < Second((fix[n => Nat => Nat](fac => fun (y: Nat) => { fac(y) }), 2))}): Nat = { 2 }


def F (x: {x: Nat, false}) = { x }

def G (x: {x: Nat, false}) = { F x }

val div = fun (x: Unit) => {fix(div => div) } in

val q: Nat = h() in
val x: Nat = 2 in
val y: Nat  = 4 in
val z: Sigma(x: Nat, Nat) = (1, 2) in
f(x + y + First(z) + f(f(2))) + g(Left(22)) / g(Right(22))
