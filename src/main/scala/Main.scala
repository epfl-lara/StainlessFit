import trees._
import interpreter._
import printer._

object Main {

  def list(l: List[Int]): Tree = l match {
    case Nil => Left(UnitLiteral)
    case h::t => Right(Tuple(Seq(NatLiteral(h), list(t))))
  }

  def main(args: Array[String]): Unit = {

    val nil = list(List())

    val cons = Lambda(
      None,
      Bind(
        Some(Var(1, "x")),
        Lambda(
          None,
          Bind(
            Some(Var(1, "l")),
            Right(Tuple(Seq(Var(1, "x"), Var(1, "l"))))
          )
        )
      )
    )

    val tail = Lambda(
      None,
      Bind(
        Some(Var(1, "l")),
        TupleSelect(Var(1, "l"), 1)
      )
    )

    val head = Lambda(
      None,
      Bind(
        Some(Var(1, "l")),
        TupleSelect(Var(1, "l"), 0)
      )
    )

    val lenBody = Lambda(
      None,
      Bind(
        Some(Var(1, "l")),
        EitherMatch(
          Var(1, "l"),
          Bind(None, NatLiteral(0)),
          Bind(
            Some(Var(1, "l")),
            Add(
              NatLiteral(1),
              App(
                App(Var(1, "len"), UnitLiteral),
                App(tail, Var(1, "l"))
              )
            )
          )
        )
      )
    )

    val len = Fix(Bind(Some(Var(1, "len")), lenBody))

    val map2Body = Lambda(
      None,
      Bind(
        Some(Var(1, "l")),
        EitherMatch(
          Var(1, "l"),
          Bind(None, nil),
          Bind(
            Some(Var(1, "l")),
            App(
              App(cons, App(Var(1, "f"), App(head, Var(1, "l")))),
              App(
                App(Var(1, "map"), UnitLiteral),
                App(tail, Var(1, "l"))
              )
            )
          )
        )
      )
    )

    val map2 = Fix(Bind(Some(Var(1, "map")), map2Body))
    val map = Lambda(None, Bind(Some(Var(1, "f")), map2))

    val lam = Lambda(
      None,
      Bind(
        Some(Var(0, "x")),
        Lambda(
          None,
          Bind(
            Some(Var(1, "y")),
            Var(1, "y")
          )
        )
      )
    )

    val appResult = App(App(lam, NatLiteral(3)), NatLiteral(4))

    val ifthenelse = IfThenElse(
      BoolLiteral(true),
      NatLiteral(2),
      NatLiteral(3)
    )

    val tupleSelect = TupleSelect(
      Tuple(
        Seq(
          BoolLiteral(true),
          BoolLiteral(false),
          NatLiteral(3))
      ),
      2
    )

    val lambdaBind = Lambda(
      None,
      Bind(
        Some(Var(1, "x")),
        Lambda(
          None,
          Bind(
            Some(Var(2, "y")),
            Var(2, "y")
          )
        )
      )
    )

    val appTest = App(lambdaBind, NatLiteral(2))

    val eqNatTest = NatEq(
      App(appTest, NatLiteral(4)),
      App(App(lambdaBind, NatLiteral(2)), NatLiteral(4))
    )

    val EitherMatchTest = EitherMatch(
      Right(NatLiteral(0)),
      Bind(Some(Var(0, "x")), Var(0, "x")),
      Bind(Some(Var(0, "x")), BoolLiteral(true))
    )

    val facBody = Lambda(
      None,
      Bind(
        Some(Var(1, "n")),
        Match(
          Var(1, "n"),
          NatLiteral(1),
          Bind(
            Some(Var(1, "m")),
            Mul(
              Var(1, "n"),
              App(
                App(Var(1, "fac"), UnitLiteral),
                Var(1, "m")
              )
            )
          )
        )
      )
    )

    val fac = Fix(
      Bind(
        Some(Var(1, "fac")),
        facBody
      )
    )

    val f = Fix(
      Bind(
        Some(Var(1, "f")),
        App(Var(1, "f"), NatLiteral(2))
      )
    )

    //val xf = App(mFac, NatLiteral(3))
    //val yf = App(fac, NatLiteral(5))
    //println(Interpretor.evaluate(xf, 10000000))
    //println(Interpretor.evaluate(xf, 100000000))

    //println(Printer.pprint(ifthenelse))
    //println(Printer.pprint(fac))

    val e = App(fac, NatLiteral(18))

    val t = TupleSelect(
      Tuple(
        Seq(
          App(fac, NatLiteral(1)),
          App(fac, NatLiteral(2)),
          App(fac, NatLiteral(3)),
          App(fac, NatLiteral(4)),
          App(fac, NatLiteral(5))
        ),
      ),
      3
    )

    val m = LetIn(None, NatLiteral(3), Bind(Some(Var(1, "x")), App(fac, Var(1, "x"))))

    val l = list(List(1, 2, 3, 4, 5, 6))

    val inc = Lambda(None, Bind(Some(Var(1, "x")), Add(NatLiteral(1), Var(1, "x"))))

    val n = Interpretor.evaluate(App(App(map, inc), l), 100000)
    println(n)
  }
}
