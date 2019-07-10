def fact(n: Nat): Nat = {
  if(n == 0) { 1 } else { fact (n - 1) * n }
}

fact 10
