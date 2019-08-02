val facFix = fix[n => {p: Nat, p < n} => Nat](fac =>
  fun (m: {m: Nat, m < n} ) => {
    fac (m - 1)
  }
) in
0
