def fact(n: Nat): Nat = {
  if(n == 0) 1 else fact (n - 1) * n
}

assert(fact 10 == 3628800)