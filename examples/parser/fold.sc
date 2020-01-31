Include("../assert.sc")

val emptyList = left ();

fun cons(n [Nat]) (l [Rec(n)(List => (Unit + (Nat, List)))]) = {
  right (n, l)
}

cons 3 (cons 2 (emptyList))
