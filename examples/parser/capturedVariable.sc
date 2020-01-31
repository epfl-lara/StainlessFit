Include("../assert.sc")

val x = 5;
fun lessThanX(y [Nat]) [returns Bool] = { y < x }

val x = 3;
val y = 4;
assert(lessThanX(x) && lessThanX(y))
