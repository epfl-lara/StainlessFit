def facFix(n: Nat): Nat = {
  Decreases(n)
  if(n == 0) 1
  else n * facFix(n - 1)
}

def fac(n : Nat) = {
  Inst(facFix, n + 1) n
}

fac(2)