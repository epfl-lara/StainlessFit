[type List[X] = Forall(n: Nat, Rec(n)(List => (Unit + (X, List))))]

fun nil[X]  [returns List[X]] = {
  [fold as List[X]](left ())
}

fun cons[X] (x [X]) (xs [List[X]])  [returns List[X]] = {
  [fold as List[X]](right ((x, xs)))
}

[type StreamN(n)[X] = Rec(n)(Stream => (X, Unit => Stream))]
[type Stream[X] = Forall(n: Nat, StreamN(n)[X])]

fun headN[X] [|n: Nat|] (s [StreamN(n)[X]])  [returns X] = {
  [unfold] val x = s;
  first x
}

fun tailN[X][|n: {n [Nat] | n > 0} |] (s [StreamN(n)[X]])  [returns StreamN(n-1)[X]] = {
  [unfold positive] val x = s;
  second x ()
}

fun head[X](s [Stream[X]])  [returns X] = {
  [unfold] val x = s;
  first x
}

fun tail[X](s [Stream[X]])  [returns Stream[X]] = {
  [unfold] val x = s;
  second x ()
}

fun constant[X](x [X]) [|n: Nat|]  [returns StreamN(n)[X]] = {
  [decreases n]
  [fold as StreamN(n)[X]]((
    x,
    keep { constant[X](x)[|n-1|] }
  ))
}

fun sum(k [Nat]) (stream [Stream[Nat]])  [returns Nat] = {
  [decreases k]
  if (k == 0) { 0 }
  else {
    [unfold] val x = stream;
    first x + sum(k - 1) (second x ())
  }
}

fun mapN[X][Y](f [X => Y])[|n: Nat|](s [StreamN(n)[X]])  [returns StreamN(n)[Y]] = {
  [decreases n]
  [fold as StreamN(n)[Y]]((
    f (headN[X][|n|](s)),
    keep { mapN[X][Y] (f) [|n-1|] (tailN[X][|n|](s)) }
  ))
}

fun map[X][Y] (f [X => Y]) (s [Stream[X]]) [returns Stream[Y]] = {
  fun of [|n: Nat|] = { mapN[X][Y](f)[|n|](s[|n|]) }
}

fun zipWithN[X][Y][Z] (f [X => Y => Z]) [|n: Nat|] (s1 [StreamN(n)[X]]) (s2 [StreamN(n)[Y]])
  [returns StreamN(n)[Z]] = {
  [decreases n]

  [fold as StreamN(n)[Z]]((
    f (headN[X][|n|](s1)) (headN[Y][|n|](s2)),
    keep {
      zipWithN[X][Y][Z] (f) [|n-1|] (tailN[X][|n|](s1)) (tailN[Y][|n|](s2))
    }
  ))
}

fun zipWith[X][Y][Z](f [X => Y => Z])(s1 [Stream[X]])(s2 [Stream[Y]])
  [returns Stream[Z]] = {

  fun of [|n: Nat|] = { zipWithN[X][Y][Z](f)[|n|](s1[|n|])(s2[|n|]) }
}

fun take[X] (k [Nat]) (s [Stream[X]]) [returns List[X]] = {
  [decreases k]
  if (k == 0) {
    nil[X]
  }
  else {
    cons[X] (head[X](s)) (take[X] (k-1) (tail[X](s)))
  }
}

fun mult (x [Nat]) (y [Nat]) = { x * y }
fun plus (x [Nat]) (y [Nat]) = { x + y }

fun fibonacci[|n: Nat|] [returns StreamN(n)[Nat]] = {
  [decreases n]
  [fold as StreamN(n)[Nat]]((
    0,
    keep {
      [fold as StreamN(n-1)[Nat]]((
        1,
        keep {
          zipWithN [Nat][Nat][Nat] plus [|n-2|] (fibonacci[|n-2|]) (tailN[Nat][|n-1|](fibonacci[|n-1|]))
        }
      ))
    }
  ))
}

take[Nat] 10 fibonacci
