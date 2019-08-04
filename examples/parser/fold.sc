def emptyList() = {
  Fold(Left(()))
}

def cons(n: Nat, l: Nat) = {
  Fold(Right((n, l)))
}

cons 3 (cons 2 (emptyList()))