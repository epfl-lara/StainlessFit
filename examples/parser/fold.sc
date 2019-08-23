Include("../assert.sc")

val emptyList = Fold(Left(())) in

def cons(n: Nat) (l: Rec(n)(list => (Unit + (Nat, list)))) = {
  Fold(Right((n, l)))
}

cons 3 (cons 2 (emptyList))
