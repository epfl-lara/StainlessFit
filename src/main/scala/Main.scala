import trees._
import interpretor._
import printer._

object Main {
  def main(args: Array[String]): Unit = {

    val lam = Lambda(
      None,
      Bind(
        Var(0, "x"),
        Lambda(
          None,
          Bind(
            Var(1, "y"),
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
        Var(1, "x"),
        Lambda(
          None,
          Bind(
            Var(2, "y"),
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

    val add = Lambda(None,
      Bind(
        Var(1, "x"),
        Fix(
          Bind(
            Var(3, "add"),
            Lambda(
              None,
              Bind(
                Var(2, "y"),
                IfThenElse(
                  NatEq(Var(2, "y"), NatLiteral(0)),
                  Var(1, "x"),
                  S(App(
                    Var(3, "add"),
                    P(Var(2, "y"))
                  )
                  )
                )
              )
            )
          )
        )
      )
    )

    val mAdd = Lambda(None,
    Bind(
      Var(1, "x"),
        Fix(
          Bind(
            Var(3, "mAdd"),
            Lambda(
              None,
              Bind(
                Var(2, "y"),
                Match(
                  Var(2, "y"),
                  Var(1, "x"),
                  Bind(
                    Var(1, "n"),
                    S(App(Var(3, "mAdd"), Var(1, "n")))
                  )
                )
              )
            )
          )
        )
      )
    )

    val mMul = Lambda(None,
      Bind(
        Var(1, "x"),
        Fix(
          Bind(
            Var(3, "mMul"),
            Lambda(
              None,
              Bind(
                Var(2, "y"),
                Match(
                  Var(2, "y"),
                  NatLiteral(0),
                  Bind(
                    Var(1, "n"),
                    App(
                      App(
                        mAdd,
                        Var(1, "x")
                      ),
                      App(
                        Var(3, "mMul"),
                        Var(1, "n")
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

    val mFac = Fix(
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


    val mul2 = Lambda(
      None,
      Bind(
        Var(1, "x"),
        IfThenElse(
          NatEq(Var(1, "x"), NatLiteral(0)),
          NatLiteral(0),
          App(App(
            add,
            NatLiteral(2)
          ),
            App(
              Var(2, "mul2"),
              P(Var(1, "x"))
            )
          )
        )
      )
    )

    val f = Fix(Bind(Var(2, "mul2"), mul2))

    val mul = Lambda(None,
      Bind(
        Var(1, "x"),
        Fix(
          Bind(
            Var(3, "mul"),
            Lambda(
              None,
              Bind(
                Var(2, "y"),
                IfThenElse(
                  NatEq(Var(2, "y"), NatLiteral(0)),
                  NatLiteral(0),
                  App(
                    App(
                      add,
                      Var(1, "x")
                    ),
                    App(
                      Var(3, "mul"),
                      P(Var(2, "y"))
                    )
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
    )

    val EitherMatchTest = EitherMatch(
      Right(NatLiteral(0)),
      Bind(Var(0, "x"), Var(0, "x")),
      Bind(Var(0, "x"), BoolLiteral(true))
    )


    val x = App(App(mMul, NatLiteral(2)), NatLiteral(3))

    val y = App(App(mul, NatLiteral(2)), NatLiteral(3))

    val xf = App(mFac, NatLiteral(3))
    val yf = App(fac, NatLiteral(5))
    //println(Interpretor.evaluate(xf, 10000000))
    println(Interpretor.evaluate(xf, 100000000))

    //println(Printer.pprint(ifthenelse))
    //println(Printer.pprint(fac))
  }
}
