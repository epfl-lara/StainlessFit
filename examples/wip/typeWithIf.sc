fun f(x: {x: Nat | x < 5}) = { x }

fun g(x: Nat) = {
  if (true) {
    val y: {x: Nat | x < 5} = 0;
    y
  }
  else {
    val y: {x: Nat | x > 5} = 10;
    y
  }
}

f (g 2)

// fun h(x: Nat) = {
//   match Left(2) {
//     case Left(x) =>
//       val y: {x: Nat | x < 5} = 0;
//       y
//     case Right(x) =>
//       val y: {x: Nat | x > 5} = 10;
//       y
//   }
// }

// f (g 2) + f (h 2)
