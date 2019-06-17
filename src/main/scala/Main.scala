import trees._
import interpreter._
import printer._

object Main {
  def main(args: Array[String]): Unit = {

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

    /*val mFac = Fix(
      Bind(
        Var(3, "mFac"),
        Lambda(
          None,
          Bind(
            Var(2, "y"),
            Match(
              Var(2, "y"),
              NatLiteral(1),
              Bind(
                Var(1, "n"),
                App(
                  App(
                    mMul,
                    S(Var(1, "n"))
                  ),
                  App(
                    Var(3, "mFac"),
                    Var(1, "n")
                  )
                )
              )
            )
          )
        )
      )
    )

    val facFun = Lambda(None,
      Bind(
        Var(1, "x"),
        IfThenElse(
          NatEq(Var(1, "x"), NatLiteral(0)),
          NatLiteral(1),
          App(
            App(
              mul,
              Var(1, "x")
            ),
            App(
              Var(2, "fac"),
              P(Var(1, "x"))
            )
          )
        )
      )
    )

    val fac = Fix(
      Bind(
        Var(2, "fac"),
        facFun
      )
    )*/

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

    val n = Interpretor.evaluate(t, 100000)
    println(n)
  }
}
