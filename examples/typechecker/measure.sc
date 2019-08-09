def measure(x: Nat) = { x }

def fac(n : Nat): Nat = {
  Decreases(measure(n))
  if(n == 0) 1
  else n * fac(n - 1)
}

fac(2)
