val sumAcc = fix[o => Nat](sumAcc =>
  fun (acc : Nat) => {
    fun (v : Unit + Nat) => {
      match v {
        case Left(x) => acc
        case Right(n) => sumAcc(n + acc)
      }
    }
  }
) in
val sum = sumAcc 0 in

assert (sum Right(42) Right(1295) Left(()) == 42 + 1295)
