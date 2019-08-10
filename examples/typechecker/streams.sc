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

val mapFix =
  Lambda X => {
    Lambda Y => {
      fun (f: X => Y) => {
        fix[n => Rec(n)(stream => (X, Unit => stream)) => Rec(n)(stream => (Y, Unit => stream))](map =>
          fun (s: Rec(n)(stream => (X, Unit => stream))) => {
            Fold[Rec(n)(stream => (Y, Unit => stream))]((
              f (Unfold(s) in (x => First(x))),
              fun (u: Unit) => {
                map (UnfoldPositive(s) in (x => (Second(x))()))
              }
            ))
          }
        )
      }
    }
  }
in

val map: Forall(X, Forall(Y, (X => Y) => Forall(n: Nat, Rec(n)(stream => (X, Unit => stream))) => Forall(n: Nat, Rec(n)(stream => (Y, Unit => stream))))) =
  Lambda X => {
    Lambda Y => {
      fun (f: X => Y) => {
        fun (s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))) => {
          fix[n => Rec(n)(stream => (Y, Unit => stream))](u =>
            Inst(mapFix[X][Y] f, n) (Inst(s, n))
          )
        }
      }
    }
  }
in

sum 15 (map[Nat][Nat] (fun (x: Nat) => { x + 5 }) (constant[Nat] 3))
