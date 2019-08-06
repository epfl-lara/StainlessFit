fix[n => Unit => Rec(n)(a => (Nat, Unit => a))]
(zero =>
  fun(x: Unit) => {
    Fold[Rec(n)(a => (Nat, Unit => a))](
      (
        0,
        fun(y: Unit) => { zero() }
      )
    )
  }
)