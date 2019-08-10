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

val zipWithFix =
  Lambda X => {
    Lambda Y => {
      Lambda Z => {
        fun (f: X => Y => Z) => {
          fix[n => Rec(n)(stream => (X, Unit => stream)) => Rec(n)(stream => (Y, Unit => stream)) => Rec(n)(stream => (Z, Unit => stream))](zipWith =>
            fun (s1: Rec(n)(stream => (X, Unit => stream))) => {
              fun (s2: Rec(n)(stream => (Y, Unit => stream))) => {
                Fold[Rec(n)(stream => (Z, Unit => stream))]((
                  f (Unfold(s1) in (x => First(x))) (Unfold(s2) in (x => First(x))),
                  fun (u: Unit) => {
                    zipWith (UnfoldPositive(s1) in (x => (Second(x))())) (UnfoldPositive(s2) in (x => (Second(x))()))
                  }
                ))
              }
            }
          )
        }
    }
    }
  }
in

val zipWith: Forall(X, Forall(Y, Forall(Z, (X => Y => Z) =>
                    Forall(n: Nat, Rec(n)(stream => (X, Unit => stream))) =>
                    Forall(n: Nat, Rec(n)(stream => (Y, Unit => stream))) =>
                    Forall(n: Nat, Rec(n)(stream => (Z, Unit => stream)))))) =
  Lambda X => {
    Lambda Y => {
      Lambda Z => {
        fun (f: X => Y => Z) => {
          fun (s1: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))) => {
            fun (s2: Forall(n: Nat, Rec(n)(stream => (Y, Unit => stream)))) => {
              fix[n => Rec(n)(stream => (Z, Unit => stream))](u =>
                Inst(zipWithFix[X][Y][Z] f, n) (Inst(s1, n)) (Inst(s2, n))
              )
            }
          }
        }
      }
    }
  }
in

val takeFix = Lambda X => {
  fix[n => Rec(n)(stream => (X, Unit => stream)) => Nat => Rec(n)(list => (Unit + (X, list)))](take =>
    fun (s: Rec(n)(stream => (X, Unit => stream))) => {
      fun (k: Nat) => {
        if(k == 0) Fold[Rec(n)(list => (Unit + (X, list)))](Left(()))
        else {
          UnfoldPositive(s) in (
            x => Fold[Rec(n)(list => (Unit + (X, list)))](Right((
              First(x),
              take ((Second(x))()) (k - 1)
            )))
          )
        }
      }
    }
  )
} in

val take: Forall(X, Forall(n: Nat, Rec(n)(stream => (X, Unit => stream))) => Nat => Forall(n: Nat, Rec(n)(list => (Unit + (X, list))))) =
  Lambda X => {
    fun (s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))) => {
      fun (k: Nat) => {
        fix[n => Rec(n)(list => (Unit + (n, list)))](u =>
          Inst(takeFix[X], k) (Inst(s, k)) k
        )
      }
    }
  }
in

def minus(x: Nat, y: Nat) = {x * y}
def plus(x: Nat, y: Nat) = {x + y}

val fibonacci =
  fix[n => Rec(n)(stream => (Nat, Unit => stream))](fibo =>
    Fold[Rec(n)(stream => (Nat, Unit => stream))]((
      0,
      fun(u: Unit) => {
          Fold[Rec(n - 1)(stream => (Nat, Unit => stream))]((
          1,
          fun (u: Unit) => {
            UnfoldPositive(fibo) in (xfib =>
              Inst(zipWithFix[Nat][Nat][Nat] plus, n - 2)
              (fibo) (UnfoldPositive(fibo) in (x => Second(x)()))
            )
          }
        ))
      }
    ))
  )
in

val x = sum 15 (zipWith[Nat][Nat][Nat] minus (constant[Nat] 2) (constant[Nat] 2)) in
val y = sum 15 (map[Nat][Nat] (fun (x: Nat) => { x + 5 }) (constant[Nat] 3)) in

val s = map[Nat][Nat] (fun (x: Nat) => { x + 1 }) (constant[Nat] 2) in
val s2 = zipWith[Nat][Nat][Nat] plus fibonacci s in
(sum 5 s2, take[Nat] s2 5)
