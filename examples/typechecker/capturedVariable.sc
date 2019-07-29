val x = 5 in
def lessThanX(y: Nat): Bool = { y < x }

val x = 3 in
val y = 4 in
lessThanX(x) && lessThanX(y)
