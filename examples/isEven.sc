val oddEven = fix(oddEven =>
  fun(p: Nat) => {
    if(p == 0) { fun(x: Nat) => { if(x == 0) true else oddEven 1 (x - 1) } }
    else { fun(x: Nat) => { if(x == 1) true else oddEven 0 (x - 1) } }
  }
) in

val x = assert(oddEven 0 0) in
val x = assert(oddEven 1 1) in
val x = assert(oddEven 0 2) in
assert (oddEven 1 3)