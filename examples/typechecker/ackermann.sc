def ackermann(m: Nat): Nat => Nat = {
  Decreases(m)
  def ack2(n: Nat): Nat = {
    Decreases(n)
    if(m == 0) n + 1
    else if(n == 0) (ackermann (m - 1)) 1
    else (ackermann (m - 1)) (ack2 (n - 1))
  }
}

ackermann 2 2