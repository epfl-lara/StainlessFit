Include("../assert.sc")

val fact = fix[n => Nat => Nat](fac =>
  fun (m: Nat) => {
      if(m == 0) 1
      else m * (fac (m - 1))
  }
) in

assert(fact 10 == 3628800)
