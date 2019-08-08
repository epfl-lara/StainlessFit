val ackermannFix = fix[o => {m: Nat, m < o} => Nat => Nat](ackermann =>
  fun (m: {m: Nat, m < o}) => {
    val f = fix[p => {d: Nat, d < p} => Nat](f =>
      fun (n: {n: Nat, n < p}) => {
        if(m == 0) n + 1
        else if(n == 0) (ackermann (m - 1)) 1
        else (ackermann (m - 1)) (f (n - 1))
      }
    ) in
    fun(n: Nat) => { Inst(f, n + 1) n }
  }
) in

def ackermann(m: Nat, n: Nat) = {
  Inst(ackermannFix, m + 1) m n
}

ackermann 2 2