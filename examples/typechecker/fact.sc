val fac = fix[n => {m: Nat, m < n} => Nat](fac =>
  fun (m: Nat) => {
      if(m == 0) 1
      else m * (fac (m - 1))
  }
) in
fac 2
