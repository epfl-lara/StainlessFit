fun ackermann(m [Nat])(n [Nat])  [returns Nat] = {
  [decreases m]
  fun ack2(n [Nat])  [returns Nat] = {
    [decreases n]
    if (m == 0) { n + 1 }
    else {
      if (n == 0) { ackermann (m - 1) 1 }
      else { ackermann (m - 1) (ack2 (n - 1)) }
    }
  }
  ack2(n)
}

ackermann 2 2
