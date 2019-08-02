val ackermann = fix[o => {m: Nat, m < o} => Nat => Nat](ackermann =>
  fun (m: {m: Nat, m < o}) => {
    fun (n: Nat) => {
      if(m == 0) n + 1
      else if((m > 0) && (n == 0)) ackermann (m - 1) 1
      else ackermann (m - 1) (ackermann m (n - 1))
    }
  }
) in ackermann