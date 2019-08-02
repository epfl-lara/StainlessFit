val oddEvenFix = fix[n => (Bool => {x: Nat, x < n} => Bool)](oddEven =>
  fun(p: Bool) => {
    if(p) { fun(x: {x: Nat, x < n}) => { if(x == 0) true else oddEven false (x - 1) } }
    else { fun(x: {x: Nat, x < n}) => { if(x == 1) true else oddEven true (x - 1) } }
  }
) in

val oddEven1Fix = fix[n => ({x: Nat, x < n} => Bool, {x: Nat, x < n} => Bool)](oddEven1 =>
  (
    fun(x: {x: Nat, x < n}) => { if(x == 0) true else Second(oddEven1) (x - 1) },
    fun(x: {x: Nat, x < n}) => { if(x == 1) true else First(oddEven1) (x - 1) }
  )
) in

def isEven(n: Nat) = {
  Inst(oddEvenFix, n + 1) true n
}

def isOdd(n: Nat) = {
  Inst(oddEvenFix, n + 1) false n
}

def isEven1(n: Nat) = {
  First(Inst(oddEven1Fix, n + 1)) n
}

def isOdd1(n: Nat) = {
  Second(Inst(oddEven1Fix, n + 1)) n
}
