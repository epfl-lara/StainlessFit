def constant[X](x: X){{n}}: Rec(n)(stream => (X, Unit => stream)) = {
  Fold[Rec(n)(stream => (X, Unit => stream))](
    (
      x,
      fun(y: Unit) => { constant{{n - 1}} }
    )
  )
}

def sum(k: Nat) (stream: Forall(n: Nat, Rec(n)(stream => (Nat, Unit => stream)))): Nat = {
  Decreases(k)
  if(k == 0) 0
  else {
    val x = (Unfold(stream) in (x => x)) in
    First(x) + sum(k - 1) (Second(x)())
  }
}

def mapFix[X][Y] (f: X => Y){{n}}(s: Rec(n)(stream => (X, Unit => stream))): Rec(n)(stream => (Y, Unit => stream)) = {
  Fold[Rec(n)(stream => (Y, Unit => stream))]((
    f (Unfold(s) in (x => First(x))),
    fun (u: Unit) => {
      mapFix {{n - 1}} (UnfoldPositive(s) in (x => (Second(x))()))
    }
  ))
}

def map[X][Y] (f: X => Y) (s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))){{n}}: Rec(n)(stream => (Y, Unit => stream)) = {
  Inst(mapFix[X][Y] f, n) (Inst(s, n))
}

def zipWithFix[X][Y][Z] (f: X => Y => Z){{n}} (s1: Rec(n)(stream => (X, Unit => stream)))
                        (s2: Rec(n)(stream => (Y, Unit => stream))): Rec(n)(stream => (Z, Unit => stream)) = {
  Fold[Rec(n)(stream => (Z, Unit => stream))]((
    f (Unfold(s1) in (x => First(x))) (Unfold(s2) in (x => First(x))),
    fun (u: Unit) => {
      zipWithFix {{n - 1}} (UnfoldPositive(s1) in (x => (Second(x))())) (UnfoldPositive(s2) in (x => (Second(x))()))
    }
  ))
}

def zipWith[X][Y][Z] (f: X => Y => Z) (s1: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream))))
                     (s2: Forall(n: Nat, Rec(n)(stream => (Y, Unit => stream)))) {{n}}: Rec(n)(stream => (Z, Unit => stream)) = {
  Inst(zipWithFix[X][Y][Z] f, n) (Inst(s1, n)) (Inst(s2, n))
}

def take2[X] (k: Nat) (s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))): Forall(n: Nat, Rec(n)(list => (Unit + (X, list)))) = {
  Decreases(k)
  if (k == 0) {
    Fold[Forall(n: Nat, Rec(n)(list => (Unit + (X, list))))](Left(()))
  }
  else {
    Unfold(s) in (x =>
      Fold[Forall(n: Nat, Rec(n)(list => (Unit + (X, list))))](Right((First(x), take2[X] (k-1) ((Second(x))()))))
    )
  }
}

def take[X] (s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))) (k: Nat) = { take2[X] k s }

def mult (x: Nat) (y: Nat) = {x * y}
def plus (x: Nat) (y: Nat) = {x + y}


def fibonacci{{n}}: Rec(n)(stream => (Nat, Unit => stream)) = {
  Fold[Rec(n)(stream => (Nat, Unit => stream))]((
    0,
    fun(u: Unit) => {
        Fold[Rec(n - 1)(stream => (Nat, Unit => stream))]((
        1,
        fun (u: Unit) => {
          UnfoldPositive(fibonacci{{n - 1}}) in (xfib =>
            Inst(zipWithFix[Nat][Nat][Nat] plus, n - 2)
              (fibonacci{{n - 1}})
              (Second(xfib)())
          )
        }
      ))
    }
  ))
}

val x = sum 15 (zipWith[Nat][Nat][Nat] mult (constant[Nat] 2) (constant[Nat] 2)) in
val y = sum 15 (map[Nat][Nat] (fun (x: Nat) => { x + 5 }) (constant[Nat] 3)) in

val s = map[Nat][Nat] (fun (x: Nat) => { x + 1 }) (constant[Nat] 2) in
val s2 = zipWith[Nat][Nat][Nat] plus fibonacci s in

(sum 5 s2, take[Nat] s2 5, take[Nat] fibonacci 10, take2[Nat] 10 fibonacci)
