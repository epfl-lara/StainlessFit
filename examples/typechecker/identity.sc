fun assert(b [{ b: Bool | b }])  [returns Unit] = { () }

fun identity(x [Nat])  [returns Nat] = { x }

fun test(f [Nat => Nat])(x [Nat]) = {
  assert(identity (f x) == f x)
}
