fix[n => Nat => Rec(n)(a => (Nat, Unit => a))]
(constant =>
  fun(x: Nat) => {
    Fold[Rec(n)(a => (Nat, Unit => a))](
      (
        x,
        fun(y: Unit) => { constant(x) }
      )
    )
  }
)