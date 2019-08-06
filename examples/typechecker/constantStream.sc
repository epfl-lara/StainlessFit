val constantFix = fix[n => Nat => Rec(n)(a => (Nat, Unit => a))]
(constant =>
  fun(x: Nat) => {
    Fold[Rec(n)(a => (Nat, Unit => a))](
      (
        x,
        fun(y: Unit) => { constant(x) }
      )
    )
  }
) in

def constant(n: Nat, x: Nat) = {
  Inst(constantFix, n + 1) x
}

val sumFix = fix[n => {k : Nat, k < n} => (Rec(n)(a => (Nat, Unit => a))) => Nat](sum =>
  fun(k: {k : Nat, k < n}) => {
    fun(stream: (Rec(k)(a => (Nat, Unit => a)))) => {
      if(k == 0) 0
      else {
        val x = (Unfold(stream) in (x => x)) in
        First(x) + sum (k - 1) (Second(x)())
      }
    }
  }
) in

def sum(k: Nat) = {
   Inst(sumFix, k + 1) k
}

sum 3 (constant 3 2)