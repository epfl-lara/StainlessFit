fun fibo(n [Nat]) [returns Nat] = {
  [decreases n]
  if (n == 0) { 0 }
  else {
    if (n == 1) { 1 }
    else { fibo(n - 1) + fibo(n - 2) }
  }
}

fibo 10
