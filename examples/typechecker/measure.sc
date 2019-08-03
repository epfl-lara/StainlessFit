def measure(x: Nat) = { x }

val facFix = fix[n => {p: Nat, measure(p) < n} => Nat](fac =>
  fun (m: {m: Nat, measure(m) < n} ) => {
    if(m == 0) 1
    else m * fac(m - 1)
  }
) in

def fac(n : Nat) = {
  Inst(facFix, n + 1) n
}

fac(2)

