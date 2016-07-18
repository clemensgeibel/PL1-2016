object Hw05Task1Sol {
  import Hw05Task2Sol._

  val minPrecedence = 0
  val addPrecedence = minPrecedence
  val mulPrecedence = 1
  val maxPrecedence = 2

  def prettyPrint(e: Exp, precedence: Int): String = {
    /**
      * Surrounds prettyPrinted with parentheses if the
      * precedence of its top operation, namely `innerPrec`,
      * is strictly smaller than the precedence of the context,
      * namely `precedence`.
      */
    def maybeParens(prettyPrinted: String, innerPrec: Int) =
      if (innerPrec < precedence)
        "(" + prettyPrinted + ")"
      else
        prettyPrinted

    e match {
      //Never surrounded by parentheses
      case Id(x)        => x.name
      case Num(n)       => n.toString
      //
      case Add(l, r)    => maybeParens(prettyPrint(l, addPrecedence) + " + " + prettyPrint(r, addPrecedence), addPrecedence)
      case Mul(l, r)    => maybeParens(prettyPrint(l, mulPrecedence) + " * " + prettyPrint(r, mulPrecedence), mulPrecedence)
      case Fun(x, body) => maybeParens(x.name + " => " + prettyPrint(body, minPrecedence), minPrecedence)
      case App(f, a)    => prettyPrint(f, maxPrecedence) + "(" + prettyPrint(a, minPrecedence) + ")"
    }
  }

  def prettyPrint(e: Exp): String = prettyPrint(e, minPrecedence)
}
/* //Examples, at the REPL;
scala> import Hw05Task1Sol._
import Hw05Task1Sol._

scala> import Hw05Task2Sol._
import Hw05Task2Sol._

scala> prettyPrint(Mul(Add(1, 2), 3))
res0: String = (1 + 2) * 3

scala> prettyPrint(Fun('x, Mul(Add(1, 2), 3)))
res1: String = x => (1 + 2) * 3

scala> prettyPrint(Fun('x, Mul(Add(1, 2), 'x)))
res2: String = x => (1 + 2) * x

scala> prettyPrint(Fun('x, Add(1, Mul(Mul(Add(Add(1, 2), 'x), 'x), 3))))
res3: String = x => 1 + (1 + 2 + x) * x * 3

scala> prettyPrint(App(Fun('x, Mul(Add(1, 2), 'x)), 1))
res4: String = (x => (1 + 2) * x)(1)

scala> prettyPrint(App(App(Fun('x, Fun('y, Mul(Mul(Add(Add(1, 2), 'y), 'x), 2))), 1), 2))
res5: String = (x => y => (1 + 2 + y) * x * 2)(1)(2)

scala> prettyPrint(App(App(Fun('x, Fun('y, Add(1, Mul(Mul(Add(Add(1, 2), 'y), 'x), 2)))), 1), 2))
res6: String = (x => y => 1 + (1 + 2 + y) * x * 2)(1)(2)
 */
