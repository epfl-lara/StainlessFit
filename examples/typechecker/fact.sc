val fac: Nat => Nat = fix[n => Nat => Nat](fac =>
  fun (m: Nat) => {
      if(m == 0) 1
      else if(m == 1) 1
      else m * (fac (m - 2))
  }
) in
fac
