def assert(b: { b: Bool | b }): Unit = { () }

def identity(x: Nat): Nat = { x }

def test(f: Nat => Nat)(x: Nat) = {
  assert(identity (f x) == f x)
}
