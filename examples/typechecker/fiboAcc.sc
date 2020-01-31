fun fiboAcc (n [Nat]) (a [Nat]) (b [Nat])  [returns Nat] = {
  [decreases n]
  if (n == 0) { a }
  else { fiboAcc (n - 1) b (a + b) }
}

fiboAcc 10 0 1
