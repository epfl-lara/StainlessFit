val id = fun of [X] (x [X]) = { x };
val add = fun of (x [Nat]) (y [Nat]) = { x + y };

fun f[X][Y] (g [PolyForall(A, A => A)]) (n [X]) (b [Y]) = {
  (g[X] n, g[Y] b)
}

f[Nat][Bool] id (add 2 3) true
