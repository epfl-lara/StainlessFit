val fiboFix = fix[n => {m: Nat, m < n} => Nat => Nat => Nat](fibo =>
  fun(m: {m : Nat, m < n}) => {
    fun(a: Nat) => {
      fun(b: Nat) => {
        if(m == 0) a
        else fibo (m - 1) b (a + b)
      }
    }
  }
) in

def fibo(n : Nat) = {
  Inst(fiboFix, n + 1) n 0 1
}

fibo 10