def fac(m: Nat): Nat = {
  Decreases(m)
  if(m == 0) 1
  else m * fac(m - 1)
}

fac(2)
