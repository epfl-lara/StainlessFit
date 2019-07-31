val oddEven = fix[n => (Nat => Nat => Bool)](oddEven =>
  fun(p: Nat) => {
    if(p == 0) { fun(x: Nat) => { if(x == 0) true else oddEven 1 (x - 1) } }
    else { fun(x: Nat) => { if(x == 1) true else oddEven 0 (x - 1) } }
  }
) in

val oddEven1 = fix[n => (Nat => Bool, Nat => Bool)](oddEven1 =>
  (
    fun(x: Nat) => { if(x == 0) true else Second(oddEven1) (x - 1) },
    fun(x: Nat) => { if(x == 1) true else First(oddEven1) (x - 1) }
  )
) in

val isEven: Nat => Bool = oddEven 0 in
val isOdd: Nat => Bool = oddEven 1 in
val isEven1: Nat => Bool = First(oddEven1) in
val isOdd1: Nat => Bool = Second(oddEven1) in ()