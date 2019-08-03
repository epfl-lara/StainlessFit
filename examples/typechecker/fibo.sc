val fiboFix = fix[n => {m: Nat, m < n} => Nat]( fibo =>
  fun(m: {m : Nat, m < n}) => {
    if(m == 0) 0
    else if(m == 1) 1
    else fibo(m - 1) + fibo(m - 2)
  }
) in

def fibo(n : Nat) = {
  Inst(fiboFix, n + 1) n
}

fibo 10