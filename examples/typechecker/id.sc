val id = fun[X] (x: X) => { x } in
val add = fun (x: Nat) (y: Nat) => { x + y } in

def f[X][Y] (g: Forall(A, A => A)) (n: X) (b: Y) = {
  (g[X] n, g[Y] b)
}

f[Nat][Bool] id (add 2 3) true