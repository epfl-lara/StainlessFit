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

f (g 2)
