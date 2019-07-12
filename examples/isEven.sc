val oddEven = fix(oddEven =>
  fun(p: Nat) => {
    if(p == 0) { fun(x: Nat) => { if(x == 0) true else oddEven 1 (x - 1) } }
    else { fun(x: Nat) => { if(x == 1) true else oddEven 0 (x - 1) } }
  }
) in

val isEven = oddEven 0 in
val isOdd = oddEven 1 in

val x = assert(isEven 0) in
val x = assert(isOdd 1) in
val x = assert(isEven 2) in
assert (isOdd 3)