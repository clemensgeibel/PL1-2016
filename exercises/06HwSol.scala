/*
## Task 1
### Part (a)
As suggested by the [lecture notes](https://github.com/ps-tuebingen/PL1-2016/blob/master/lecturenotes/12-syntacticvsmeta.scala#L51), reimplement the Compositional interpreter as an internal visitor.

### Part (b)
Try the same exercise with the standard environment-based FAE interpreter.
 */

object Hw06SolTask1 {
  //First, FAE expressions and visitor infrastructure
  sealed abstract class Exp
  case class Num(n: Int) extends Exp
  case class Id(name: Symbol) extends Exp
  case class Add(lhs: Exp, rhs: Exp) extends Exp
  case class Fun(param: Symbol, body: Exp) extends Exp
  case class App(funExpr: Exp, argExpr: Exp) extends Exp

  case class ExpVisitor[T](
    num: Int => T,
    id: Symbol => T,
    add: (T, T) => T,
    fun: (Symbol, T) => T,
    app: (T, T) => T)

  def visit[T](v: ExpVisitor[T], e: Exp): T = e match {
    case Num(n) => v.num(n)
    case Id(name) => v.id(name)
    case Add(lhs, rhs) => v.add(visit(v, lhs), visit(v, rhs))
    case Fun(param, body) => v.fun(param, visit(v, body))
    case App(funExpr, argExpr) => v.app(visit(v, funExpr), visit(v, argExpr))
  }

  //Instead of defining ExpVisitor like above, we can also use an object algebra
  //interface:
  trait ExpOA[T] {
    implicit def num(n: Int): T
    implicit def id(name: Symbol): T
    def add(e1: T, e2: T): T
    def fun(param: Symbol, body: T): T
    def app(funExpr: T, argExpr: T): T
    def wth(x: Symbol, xdef: T, body: T): T = app(fun(x, body), xdef)
  }

  //Compositional interpreter from lecture:
  object Compositional {
    sealed abstract class Value
    type Env = Map[Symbol, Value]
    case class NumV(n: Int) extends Value
    //PG: Pay attention to the definition of FunV! It takes a function from Value to Value!
    case class FunV(f: Value => Value) extends Value

    def eval(e: Exp): Env => Value = e match {
      case Num(n: Int) => (env) => NumV(n)
      case Id(x) => env => env(x)
      case Add(l, r) => { (env) =>
        (eval(l)(env), eval(r)(env)) match {
          case (NumV(v1), NumV(v2)) => NumV(v1 + v2)
          case _                    => sys.error("can only add numbers")
        }
      }
      case Fun(param, body) => (env) => FunV((v) => eval(body)(env + (param -> v)))
      case App(f, a) => (env) => (eval(f)(env), eval(a)(env)) match {
        // Use environment stored in closure to realize proper lexical scoping!
        case (FunV(g), arg) => g(arg)
        case _              => sys.error("can only apply functions")
      }
    }

    //Task1 (a): and expressed as a visitor:
    val compositionalVisitor =
      ExpVisitor[Env => Value](
        n => env =>
          NumV(n),
        x => env =>
          env(x),
        (l, r) => env =>
          (l(env), r(env)) match {
            case (NumV(v1), NumV(v2)) => NumV(v1 + v2)
            case _                    => sys.error("can only add numbers")
          },
        (param, body) => env =>
          FunV((v) => body(env + (param -> v))),
        (funV, argV) => env =>
          (funV(env), argV(env)) match {
            // Use environment stored in closure to realize proper lexical scoping!
            case (FunV(g), arg) => g(arg)
            case _              => sys.error("can only apply functions")
          })
  }

  //Standard environment-based FAE interpreter, for reference:
  object FAE {
    sealed abstract class Value
    type Env = Map[Symbol, Value]
    case class NumV(n: Int) extends Value
    //PG: standard closure
    case class ClosureV(f: Fun, env: Env) extends Value

    def eval(e: Exp, env: Env): Value = e match {
      case Num(n: Int) => NumV(n)
      case Id(x)       => env(x)
      case Add(l, r) => {
        (eval(l, env), eval(r, env)) match {
          case (NumV(v1), NumV(v2)) => NumV(v1 + v2)
          case _                    => sys.error("can only add numbers")
        }
      }
      case f @ Fun(param, body) => ClosureV(f, env)
      case App(f, a) => eval(f, env) match {
        // Use environment stored in closure to realize proper lexical scoping!
        case ClosureV(f, closureEnv) => eval(f.body, closureEnv + (f.param -> eval(a, env)))
        case _                       => sys.error("can only apply functions")
      }
    }
  }
  //Task1 (b):
  //Try the same exercise with the standard environment-based FAE interpreter.
  object FAECompositional {
    sealed abstract class Value
    type Env = Map[Symbol, Value]
    //PG: a closure would store a Fun, that is the parameter name and the body.
    //But we have the *evaluated* body. So store that!
    case class ClosureV(f: Env => Value, param: Symbol, env: Env) extends Value
    case class NumV(n: Int) extends Value

    val faeInterpreterVisitor =
      ExpVisitor[Env => Value](
        n => env =>
          NumV(n),
        name => env =>
          env(name),
        (l, r) => env =>
          (l(env), r(env)) match {
            case (NumV(n1), NumV(n2)) => NumV(n1 + n2)
            case _                    => sys.error("can only add numbers")
          },
        (param, body) => env =>
          ClosureV(body, param, env),
        (funExpr, argExpr) => env =>
          funExpr(env) match {
            case ClosureV(f, param, closureEnv) => f(closureEnv + (param -> argExpr(closureEnv)))
            case _                              => sys.error("can only apply functions")
          })

    //As an extra: the *same* interpreter (with the same variable names) as an object algebra.
    trait FAEInterpreterOA extends ExpOA[Env => Value] {
      def num(n: Int) = env =>
        NumV(n)

      def id(name: Symbol) = env =>
        env(name)

      def add(l: Env => Value, r: Env => Value) = env =>
        (l(env), r(env)) match {
          case (NumV(n1), NumV(n2)) => NumV(n1 + n2)
          case _                    => sys.error("can only add numbers")
        }

      def fun(param: Symbol, body: Env => Value) = env =>
        ClosureV(body, param, env)

      def app(funExpr: Env => Value, argExpr: Env => Value) = env =>
        funExpr(env) match {
          case ClosureV(f, param, closureEnv) => f(closureEnv + (param -> argExpr(closureEnv)))
          case _                              => sys.error("can only apply functions")
        }
    }
    object FAEInterpreterOA extends FAEInterpreterOA
  }
}

object Hw06SolTask2 {
  sealed abstract class Exp
  case class Id(name: Symbol) extends Exp
  implicit def id2exp(s: Symbol) = Id(s)
  case class Fun(param: Symbol, body: Exp) extends Exp
  case class App(funExpr: Exp, argExpr: Exp) extends Exp

  /*
## Task 2
In the lecture on Church encodings, we have seen Church encodings in FAE of booleans, numerals and operations on them.  This exercise requires you to use them to accomplish some simple programming tasks.

1. We have seen how the exponent operation `exp` is defined in terms of `mult` and `one`.  Give a similar definition of `mult` in terms of `add` and `zero` (unlike the one presented in the lecture).
2. Study carefully how `multlist` works.  Then define a function called `sumlist` that sums all Church-numerals in a list.
3. Define a function called `allzeros` that tests whether a list of Church numerals are all zeros.

Do not forget to test your definitions.
   */

  //From the lecture.
  //Numbers:
  val zero = Fun('s, Fun('z, 'z))
  val succ = Fun('n, Fun('s, Fun('z, App('s, App(App('n, 's), 'z)))))
  val one = App(succ, zero)
  val add = Fun('a, Fun('b, Fun('s, Fun('z, App(App('a, 's), App(App('b, 's), 'z))))))

  val mult = Fun('a, Fun('b, Fun('s, Fun('z, App(App('a, App('b, 's)), 'z)))))
  val exp = Fun('a, Fun('b, App(App('b, App(mult, 'a)), one)))
  //Task 2.1
  val mult2 = Fun('a, Fun('b, App(App('b, App(add, 'a)), zero)))

  //Task 2.2
  val sumlist = Fun('l, App(App('l, add), zero))
  def sumlistScala(l: List[Int]) = l.foldRight(0)(_ + _)

  def allzeroScala(l: List[Int]) =
    l.foldRight(true)((n, acc) => acc && iszeroScala(n))
  def iszeroScala(n: Int) = n == 0

  //Booleans:
  val f = Fun('t, Fun('f, 'f)) // false
  val t = Fun('t, Fun('f, 't)) // true
  val and = Fun('a, Fun('b, App(App('a, 'b), 'a)))
  val or = Fun('a, Fun('b, App(App('a, 'a), 'b)))
  val not = Fun('a, Fun('t, Fun('f, App(App('a, 'f), 't))))
  //Task 2.3
  val iszero = Fun('a, App(App('a, Fun('x, f)), t))

  val allzero =
    Fun('l,
      App(App('l,
        Fun('n, Fun('acc,
          App(App(and,
            'acc),
            App(iszero, 'n))))),
        t))

  val emptylist = Fun('c, Fun('e, 'e))
  val cons = Fun('h, Fun('r, Fun('c, Fun('e, App(App('c, 'h), App(App('r, 'c), 'e))))))

  /* Here is the list 0, 0, 0 */
  val list000 = App(App(cons, zero), App(App(cons, zero), App(App(cons, zero), emptylist)))

  /* Here is the list 0, 1, 0 */
  val list010 = App(App(cons, zero), App(App(cons, one), App(App(cons, zero), emptylist)))
}

//Material on Church-encoding for the exercise, including (below) the solution to task 3
object ChurchLesson {
  //Distinct from the standard Boolean type, but equivalent (technically,
  //isomorphic) to it.
  sealed trait Bool
  case class True() extends Bool
  case class False() extends Bool

  case class BooleanVisitor[T](t: T, f: T)
  def foldBoolean[T](b: Bool)(bv: BooleanVisitor[T]): T = b match {
    case True()  => bv.t
    case False() => bv.f
  }

  def trueChurch[T](t: T)(f: T): T = t //Fun('t, Fun('f, 't))
  def falseChurch[T](t: T)(f: T): T = f //Fun('t, Fun('f, 'f))

  //trueChurch = foldBoolean(True()) _
  //falseChurch = foldBoolean(False()) _

  //Peano naturals.
  sealed trait Nat
  case class Succ(n: Nat) extends Nat
  case class Zero() extends Nat

  //case class NatExternalVisitor[T](zero: T, succ: Nat => T)
  case class NatVisitor[T](succ: T => T, zero: T)
  def pred(n: Nat): Nat = n match {
    case Succ(n) => n
    case Zero()  => Zero()
  }
  def foldNat[T](n: Nat)(nv: NatVisitor[T]): T = n match {
    case Succ(n) => nv.succ(foldNat(n)(nv))
    case Zero()  => nv.zero
  }
  type ChurchNat[T] = (T => T) => T => T
  def zeroChurch[T](succ: T => T, zero: T): T = zero //Fun('s, Fun('z, 'z))
  //zeroChurch == foldNat(Zero()) _
  def oneChurch[T](succ: T => T, zero: T): T = succ(zero) //Fun('s, Fun('z, App('s, 'z)))
  //oneChurch == foldNat(Succ(Zero())) _

  def succChurch[T](n: ChurchNat[T])(succ: T => T, zero: T): T =
    succ(n(succ)(zero))
  //Fun('n, Fun('s, Fun('z, App('s, App(App('n, 's),'z)))))
  //succChurch(foldNat(n)) == foldNat(Succ(n)) _

  //We could Church-encode also Either. We could use a specialized variant:
  trait EitherIntBool
  case class LeftInt(i: Int) extends EitherIntBool
  case class RightBool(b: Bool) extends EitherIntBool
  //And we can also Church-encode pairs. Say, for simplicity, pairs of Int.
  trait IPairIntInt
  case class PairIntInt(a: Int, b: Int) extends IPairIntInt
}

object ChurchBooleans {
  //Distinct from the standard Boolean type, but equivalent (technically,
  //isomorphic) to it.
  sealed trait Bool
  case class True() extends Bool
  case class False() extends Bool

  //Internal visitors for Booleans.
  case class BooleanVisitor[T](t: T, f: T)
  def visitBoolean[T](b: Bool)(bv: BooleanVisitor[T]): T = b match {
    case True()  => bv.t
    case False() => bv.f
  }
  //Fold over booleans. Note this code is very similar to visitBoolean;
  //the only difference is that we get the members of BooleanVisitor as separate arguments.
  //Also, note that this is very similar to an if (ignoring the evaluation order).
  def foldBoolean[T](b: Bool)(t: T, f: T): T = b match {
    case True()  => t
    case False() => f
  }

  def trueChurch[T](t: T)(f: T): T = t //Fun('t, Fun('f, 't))
  def falseChurch[T](t: T)(f: T): T = f //Fun('t, Fun('f, 'f))

  //trueChurch = foldBoolean(True()) _
  //falseChurch = foldBoolean(False()) _
}
object ChurchNats {
  //Peano naturals.
  sealed trait Nat
  case class Succ(n: Nat) extends Nat
  case class Zero() extends Nat

  case class NatVisitor[T](succ: T => T, zero: T)
  //Contrast with:
  //case class NatExternalVisitor[T](zero: T, succ: Nat => T)

  //Traverse a Nat to produce a result using an internal visitor.
  def visitNat[T](n: Nat)(nv: NatVisitor[T]): T = n match {
    case Succ(n) => nv.succ(visitNat(n)(nv))
    case Zero()  => nv.zero
  }

  //Fold over naturals. Note this code is very similar to visitNat;
  //the only difference is that we get the members of NatVisitor as separate arguments.
  def foldNat[T](n: Nat)(succ: T => T, zero: T): T = n match {
    case Succ(n) => succ(foldNat(n)(succ, zero))
    case Zero()  => zero
  }
  //A function that is not structurally recursive, hence cannot be written directly as a fold.
  def pred(n: Nat): Nat = n match {
    case Succ(n) => n
    case Zero()  => Zero()
  }

  //This is a type of a curried function — which is the type of Church-numbers expressed in Scala
  type ChurchNat[T] = (T => T) => T => T

  def zeroChurch[T](succ: T => T)(zero: T): T = zero //Fun('s, Fun('z, 'z))
  //zeroChurch[T] has type ChurchNat[T]:
  def zeroChurchNat[T]: ChurchNat[T] = zeroChurch[T]
  //We can write that directly as:
  def zeroChurchNat2[T]: ChurchNat[T] = succ => zero => zero

  //zeroChurch == foldNat(Zero()) _
  def oneChurch[T](succ: T => T)(zero: T): T = succ(zero) //Fun('s, Fun('z, App('s, 'z)))
  //oneChurch == foldNat(Succ(Zero())) _

  //Also oneChurch[T] has type ChurchNat[T]:
  def oneChurchNat[T]: ChurchNat[T] = oneChurch[T]
  //We can write that directly as:
  def oneChurchNat2[T]: ChurchNat[T] = succ => zero => succ(zero)

  def succChurch[T](n: ChurchNat[T])(succ: T => T)(zero: T): T =
    succ(n(succ)(zero))
  //Fun('n, Fun('s, Fun('z, App('s, App(App('n, 's),'z)))))
  //succChurch(foldNat(n)) == foldNat(Succ(n)) _

  //We could Church-encode also Either. We could use a specialized variant:
  sealed trait EitherIntBoolean
  case class LeftInt(i: Int) extends EitherIntBoolean
  case class RightBool(b: Boolean) extends EitherIntBoolean
  //And we can also Church-encode pairs. Say, for simplicity, pairs of Int.
  sealed trait IPairIntInt
  case class PairIntInt(a: Int, b: Int) extends IPairIntInt

  //Task 3
  def foldPairIntInt[T](p: PairIntInt)(f: Int => Int => T): T = f(p.a)(p.b)
  type ChurchPairIntInt[T] = (Int => Int => T) => T
  def pair[T](a: Int)(b: Int): ChurchPairIntInt[T] = f => f(a)(b)
}

object ChurchList {
  sealed trait ListInt
  case class NilInt() extends ListInt
  case class ConsInt(head: Int, tail: ListInt) extends ListInt
  case class ListIntVisitor[T](nilInt: T, consInt: Int => T => T)
  def visitListInt[T](l: ListInt)(lv: ListIntVisitor[T]): T = l match {
    case NilInt()            => lv.nilInt
    case ConsInt(head, tail) => lv.consInt(head)(visitListInt(tail)(lv))
  }
  //This corresponds to the method foldRight in the standard library.
  def foldListInt[T](l: ListInt)(nilInt: T, consInt: Int => T => T): T = l match {
    case NilInt()            => nilInt
    case ConsInt(head, tail) => consInt(head)(foldListInt(tail)(nilInt, consInt))
  }
  type ChurchListInt[T] = T => (Int => T => T) => T
  def churchNil[T]: ChurchListInt[T] = nilInt => consInt => nilInt
  def churchCons[T](head: Int, tail: ChurchListInt[T]): ChurchListInt[T] = nilInt => consInt => consInt(head)(tail(nilInt)(consInt))
}
/*
Let's use beta-equivalence to show that:
and(true, x) beta-== x

Church-encodings from lecture:
val t = Fun('t, Fun('f, 't)) // That is, t => f => t
val and = Fun('a, Fun('b, App(App('a, 'b),'a))) // That is, a => b => a(b)(a)

So we must show:
(a => b => a(b)(a))(t => f => t) beta-== (x => x)

We beta-reduce the LHS to get:
(a => b => a(b)(a))(t => f => t) beta-==
b => (t => f => t)(b)(t => f => t) beta-==
b => b
*/
