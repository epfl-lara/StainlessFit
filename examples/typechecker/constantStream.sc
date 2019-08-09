val constant: Forall(X, X => Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))) =
  Lambda X => {
    fun(x: X) => {
      fix[n => Rec(n)(stream => (X, Unit => stream))] (constant =>
        Fold[Rec(n)(stream => (X, Unit => stream))](
          (
            x,
            fun(y: Unit) => { constant }
          )
        )
      )
    }
  } in

val sumFix = fix[n => {k : Nat, k < n} => Forall(n: Nat, Rec(n)(stream => (Nat, Unit => stream))) => Nat](sum =>
  fun(k: {k : Nat, k < n}) => {
    fun(stream: Forall(n: Nat, Rec(n)(stream => (Nat, Unit => stream)))) => {
      if(k == 0) 0
      else {
        val x = (Unfold(stream) in (x => x)) in
        First(x) + sum(k - 1) (Second(x)())
      }
    }
  }
) in

def sum(k: Nat) = {
  Inst(sumFix, k + 1) k
}

sum 15 (constant[Nat] 3)
