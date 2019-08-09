def fiboAcc(n : Nat): Nat => Nat => Nat = {
  Decreases(n)
  def aux(a: Nat, b: Nat) = {
    if(n == 0) a
    else fiboAcc (n - 1) b (a + b)
  }
}

fiboAcc 10 0 1