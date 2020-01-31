Include("../assert.sc")

val oddEven = fix[n => (Nat => Nat => Bool)](oddEven =>
  fun of (p [Nat]) = {
    if (p == 0) { fun of (x [Nat]) = { if (x == 0) true else oddEven 1 (x - 1) } }
    else { fun of (x [Nat]) = { if (x == 1) true else oddEven 0 (x - 1) } }
  }
);

val oddEven1 = fix[n => (Nat => Bool, Nat => Bool)](oddEven1 =>
  (
    fun of (x [Nat]) = { if (x == 0) true else second oddEven1 (x - 1) },
    fun of (x [Nat]) = { if (x == 1) true else first oddEven1 (x - 1) }
  )
);

val isEven = oddEven 0;
val isOdd = oddEven 1;
val isEven1 = first oddEven1;
val isOdd1 = second oddEven1;
val x = assert(isEven 0 && isEven1 0);
val x = assert(isOdd 1 && isOdd1 1);
val x = assert(isEven 2 && isEven1 2);

assert(isOdd 3 && isOdd1 3)
