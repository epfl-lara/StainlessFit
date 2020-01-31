Include("../assert.sc")

val sumAcc = fix[o => Nat](sumAcc =>
  fun of (acc [Nat]) = {
    fun of (v [Unit + Nat]) = {
      match v {
        case left(x) => acc
        case right(n) => sumAcc(n + acc)
      }
    }
  }
);
val sum = sumAcc 0;

assert (sum (right 42) (right 1295) (left (())) == 42 + 1295)
