val oddEven = fix[n => (Bool => {x: Nat, x < n} => Bool)](oddEven =>
  fun(p: Bool) => {
    if(p) { fun(x: {x: Nat, x < n}) => { if(x == 0) true else oddEven false (x - 1) } }
    else { fun(x: {x: Nat, x < n}) => { if(x == 1) true else oddEven true (x - 1) } }
  }
) in

val oddEven1 = fix[n => ({x: Nat, x < n} => Bool, {x: Nat, x < n} => Bool)](oddEven1 =>
  (
    fun(x: {x: Nat, x < n}) => { if(x == 0) true else Second(oddEven1) (x - 1) },
    fun(x: {x: Nat, x < n}) => { if(x == 1) true else First(oddEven1) (x - 1) }
  )
) in oddEven

//val isEven = oddEven 0 in
//val isOdd = oddEven 1 in
//val isEven1 = First(oddEven1) in
//val isOdd1 = Second(oddEven1) in isEven