val oddEven = fix[n => (Nat => Nat)](oddEven =>
  fun(p: Nat) => {
    if(p == 0) { fun(x: Nat) => { if(x == 0) true else oddEven 1 (x - 1) } }
    else { fun(x: Nat) => { if(x == 1) true else oddEven 0 (x - 1) } }
  }
) in

val oddEven1 = fix[n => (Nat => Nat)](oddEven1 =>
    (
      fun(x: Nat) => { if(x == 0) true else Second(oddEven1) (x - 1) },
      fun(x: Nat) => { if(x == 1) true else First(oddEven1) (x - 1) }
    )
) in

val isEven = oddEven 0 in
val isOdd = oddEven 1 in
val isEven1 = First(oddEven1) in
val isOdd1 = Second(oddEven1) in
val x = assert(isEven 0 && isEven1 0) in
val x = assert(isOdd 1 && isOdd1 1) in
val x = assert(isEven 2 && isEven1 2) in
assert(isOdd 3 && isOdd1 3)