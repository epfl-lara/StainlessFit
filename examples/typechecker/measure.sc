fun measure(x [Nat]) = { x }

fun fac(n [Nat])  [returns Nat] = {
  [decreases measure(n)]
  if (n == 0) 1
  else n * fac(n - 1)
}

fac(2)
