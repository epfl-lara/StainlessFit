fix[n => Rec(n)(stream => (Nat, Unit => stream))]
(zero =>
  Fold[Rec(n)(stream => (Nat, Unit => stream))]((
    0,
    fun(y: Unit) => { zero }
  ))
)