Include("../assert.sc")
Include("../assert.sc")

val x = (
  val x = 5;
  fun f(x [Nat])  [returns Nat] = { 2 * x }
  val x = f(x);
  x - x
);
x == 0
