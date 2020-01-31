fun parity(n [Nat]) (b [Bool])  [returns Bool] = {
  [decreases n]
  if (b) {
    if (n == 0) true else parity (n - 1) false
  }
  else {
    if (n == 0) false else if (n == 1) true else parity (n - 1) true
  }
}

fun parity1(n [Nat]) [returns (Bool, Bool)] = {
  [decreases n]
  if (n == 0) (true, false)
  else { val x = parity1 (n - 1); (second x, first x) }
}

fun isEven(n [Nat]) = { parity n true }
fun isOdd(n [Nat]) = { parity n false }
fun isEven1(n [Nat]) = { first (parity1 n) }
fun isOdd1(n [Nat]) = { second (parity1 n) }

isEven1 2
