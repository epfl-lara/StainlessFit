def parity(n: Nat): Bool => Bool = {
  Decreases(n)
  def f(b: Bool): Bool = {
    if(b) {
      if(n == 0) true else parity (n - 1) false
    }
    else {
      if(n == 0) false else if (n == 1) true else parity (n - 1) true
    }
  }
}

def parity1(n: Nat): (Bool, Bool) = {
  Decreases(n)
  if(n == 0) (true, false)
  else { val x = parity1 (n - 1) in (Second(x), First(x)) }
}

def isEven(n: Nat) = { parity n true }
def isOdd(n: Nat) = { parity n false }
def isEven1(n: Nat) = { First(parity1 n) }
def isOdd1(n: Nat) = { Second(parity1 n) }

isEven1 2