def fiboAcc (n : Nat) (a: Nat) (b: Nat): Nat = {
  Decreases(n)
  if(n == 0) a
  else fiboAcc (n - 1) b (a + b)
}

fiboAcc 10 0 1