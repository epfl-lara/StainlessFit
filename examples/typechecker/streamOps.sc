val map =
  Lambda X => {
    Lambda Y => {
      fun (f: X => Y) => {
        fix[n => Rec(n)(stream => (X, Unit => stream)) => Rec(n)(stream => (Y, Unit => stream))](map =>
          fun (s: Rec(n)(stream => (X, Unit => stream))) => {
            Fold[Rec(n)(stream => (Y, Unit => stream))]((
              f (Unfold(s) in (x => First(x))),
              fun (u: Unit) => {
                map (UnfoldPositive(s) in (x => (Second(x))()))
              }
            ))
          }
        )
      }
    }
  }
in
map
