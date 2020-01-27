def headN[X]{n: Nat}(s: Rec(n)(stream => (X, Unit => stream))): X = {
  Unfold(s) in (x => First(x))
}

def tailN[X]{ n: {n: Nat | n > 0} }(s: Rec(n)(stream => (X, Unit => stream))): Rec(n-1)(stream => (X, Unit => stream)) = {
  UnfoldPositive(s) in (x => (Second(x))())
}

def head[X](s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))): X = {
  Unfold(s) in (x => First(x))
}

def tail[X](s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))): Forall(n: Nat, Rec(n)(stream => (X, Unit => stream))) = {
  Unfold(s) in (x => (Second(x))())
}

def constant[X](x: X){n: Nat}: Rec(n)(stream => (X, Unit => stream)) = {
  Decreases(n)
  Fold[Rec(n)(stream => (X, Unit => stream))](
    (
      x,
      fun(y: Unit) => { constant[X](x){n - 1} }
    )
  )
}

def sum(k: Nat) (stream: Forall(n: Nat, Rec(n)(stream => (Nat, Unit => stream)))): Nat = {
  Decreases(k)
  if (k == 0) 0
  else {
    val x = (Unfold(stream) in (x => x)) in
    First(x) + sum(k - 1) (Second(x)())
  }
}

def mapN[X][Y] (f: X => Y){n: Nat}(s: Rec(n)(stream => (X, Unit => stream))): Rec(n)(stream => (Y, Unit => stream)) = {
  Decreases(n)
  Fold[Rec(n)(stream => (Y, Unit => stream))]((
    f (headN[X]{n}(s)),
    fun (u: Unit) => { mapN[X][Y] (f) {n - 1} (tailN[X]{n}(s)) }
  ))
}

def map[X][Y] (f: X => Y) (s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))): Forall(n: Nat, Rec(n)(stream => (Y, Unit => stream))) = {
  fun {n: Nat} => { mapN[X][Y](f){n}(s{n}) }
}

def zipWithN
  [X][Y][Z]
  (f: X => Y => Z)
  {n: Nat}
  (s1: Rec(n)(stream => (X, Unit => stream)))
  (s2: Rec(n)(stream => (Y, Unit => stream))):
    Rec(n)(stream => (Z, Unit => stream)) = {

  Decreases(n)

  Fold[Rec(n)(stream => (Z, Unit => stream))]((
    f (headN[X]{n}(s1)) (headN[Y]{n}(s2)),
    fun (u: Unit) => {
      zipWithN[X][Y][Z] (f) {n - 1} (tailN[X]{n}(s1)) (tailN[Y]{n}(s2))
    }
  ))
}

def zipWith
  [X][Y][Z]
  (f: X => Y => Z)
  (s1: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream))))
  (s2: Forall(n: Nat, Rec(n)(stream => (Y, Unit => stream)))):
    Forall(n: Nat, Rec(n)(stream => (Z, Unit => stream))) = {

  fun {n: Nat} => { zipWithN[X][Y][Z](f){n}(s1{n})(s2{n}) }
}

def nil[X]: Forall(n: Nat, Rec(n)(list => (Unit + (X, list)))) = {
  Fold[Forall(n: Nat, Rec(n)(list => (Unit + (X, list))))](Left(()))
}

def cons[X](x: X)(xs: Forall(n: Nat, Rec(n)(list => (Unit + (X, list))))): Forall(n: Nat, Rec(n)(list => (Unit + (X, list)))) = {
  Fold[Forall(n: Nat, Rec(n)(list => (Unit + (X, list))))](Right((x, xs)))
}

def take[X] (k: Nat) (s: Forall(n: Nat, Rec(n)(stream => (X, Unit => stream)))): Forall(n: Nat, Rec(n)(list => (Unit + (X, list)))) = {
  Decreases(k)
  if (k == 0) {
    nil[X]
  }
  else {
    cons[X] (head[X](s)) (take[X] (k-1) (tail[X](s)))
  }
}

def mult (x: Nat) (y: Nat) = { x * y }
def plus (x: Nat) (y: Nat) = { x + y }

def fibonacci{n: Nat}: Rec(n)(stream => (Nat, Unit => stream)) = {
  Decreases(n)
  Fold[Rec(n)(stream => (Nat, Unit => stream))]((
    0,
    fun(u: Unit) => {
      Fold[Rec(n - 1)(stream => (Nat, Unit => stream))]((
        1,
        fun (u: Unit) => {
          zipWithN [Nat][Nat][Nat] plus {n - 2} (fibonacci{n - 2}) (tailN[Nat]{n-1}(fibonacci{n - 1}))
        }
      ))
    }
  ))
}

take[Nat] 10 fibonacci
