import scala.language.higherKinds
import scala.language.implicitConversions

object Hw09Sol {
  //Task 1
  object OriginalVersion {
    //These definitions are reused before and after lambda lifting:
    def map(xs: List[Int])(f: Int => Int): List[Int] = xs match {
      case Nil => Nil
      case x :: xs => f(x) :: map(xs)(f)
    }

    def flatMap(xs: List[Int])(f: Int => List[Int]): List[Int] = xs match {
      case Nil => Nil
      case x :: xs => f(x) ++ flatMap(xs)(f)
    }

    object BeforeLambdaLifting {
      def map2(xs: List[Int])(f: Int => Int): List[Int] = flatMap(xs) {
        x => List(f(x))
      }

      def caller1(l: List[Int]) =
        map(l)(x => x + 1) ++
          map(List(1, 2, 3))(x => x + 2)

      def caller2(l: List[Int]) =
        map(List(1, 2, 3))(x => x + 1) ++
          map(map(l)(x => x + 2))(y => y * 2)

      def caller3(l: List[Int]) =
        flatMap(List(1, 2, 3))(x =>
          map(List(x + 1))(y =>
            x + y))

      def caller4(l: List[Int]) =
        flatMap(List(1, 2, 3))(x =>
          map2(List(x * 3))(y =>
            x + y + 42))
    }

    object AfterLambdaLifting {
      //map2 and lifted functions
      def listF(f: Int => Int)(x: Int) =
        List(f(x))

      def map2(xs: List[Int])(f: Int => Int): List[Int] =
        flatMap(xs)(listF(f))

      //Caller1 and lifted functions
      def plus1(x: Int) = x + 1

      def plus2(x: Int) = x + 2

      def caller1(l: List[Int]) =
        map(l)(plus1) ++
          map(List(1, 2, 3))(plus2)

      //Caller2 and lifted functions
      def times2(x: Int) = x * 2

      def caller2(l: List[Int]) =
        map(List(1, 2, 3))(plus1) ++
          map(map(l)(plus2))(times2)

      //Caller3 and lifted functions
      def plusxy(x: Int)(y: Int) = x + y

      def mapListPlus1Plusxyx(x: Int) =
        map(List(x + 1))(plusxy(x))

      def caller3(l: List[Int]) =
        flatMap(List(1, 2, 3))(mapListPlus1Plusxyx)

      //Caller4 and lifted functions
      def plusxy42(x: Int)(y: Int) = x + y + 42

      def map2ListTimes3Plusxy42(x: Int) =
        map2(List(x * 3))(plusxy42(x))

      def caller4(l: List[Int]) =
        flatMap(List(1, 2, 3))(map2ListTimes3Plusxy42)
    }
  }

  object Defunctionalized {
    //We need separate traits for different function types:
    sealed trait FunctionValueIntInt
    case class Plus1() extends FunctionValueIntInt
    case class Plus2() extends FunctionValueIntInt
    case class Times2() extends FunctionValueIntInt
    case class Plusxy(x: Int) extends FunctionValueIntInt
    case class Plusxy42(x: Int) extends FunctionValueIntInt

    def applyIntInt(f: FunctionValueIntInt, arg: Int): Int = f match {
      case Plus1() => arg + 1
      case Plus2() => arg + 2
      case Times2() => arg * 2
      case Plusxy(x) => x + arg
      case Plusxy42(x) => x + arg + 42
    }

    sealed trait FunctionValueIntListInt
    case class ListF(f: FunctionValueIntInt) extends FunctionValueIntListInt
    case class MapListPlus1Plusxyx() extends FunctionValueIntListInt
    case class Map2ListTimes3Plusxy42() extends FunctionValueIntListInt

    def applyIntListInt(f: FunctionValueIntListInt, x: Int): List[Int] = f match {
      case ListF(f) => List(applyIntInt(f, x))
      case MapListPlus1Plusxyx() => map(List(x + 1))(Plusxy(x))
      case Map2ListTimes3Plusxy42() => map2(List(x * 3))(Plusxy42(x))
    }

    def map(xs: List[Int])(f: FunctionValueIntInt): List[Int] = xs match {
      case Nil => Nil
      case x :: xs => applyIntInt(f, x) :: map(xs)(f)
    }

    def flatMap(xs: List[Int])(f: FunctionValueIntListInt): List[Int] = xs match {
      case Nil => Nil
      case x :: xs => applyIntListInt(f, x) ++ flatMap(xs)(f)
    }

    def map2(xs: List[Int])(f: FunctionValueIntInt): List[Int] = flatMap(xs)(ListF(f))

    def caller1(l: List[Int]) =
      map(l)(Plus1()) ++
        map(List(1, 2, 3))(Plus2())

    def caller2(l: List[Int]) =
      map(List(1, 2, 3))(Plus1()) ++
        map(map(l)(Plus2()))(Times2())

    def caller3(l: List[Int]) =
      flatMap(List(1, 2, 3))(MapListPlus1Plusxyx())

    def caller4(l: List[Int]) =
      flatMap(List(1, 2, 3))(Map2ListTimes3Plusxy42())
  }

  //In the exercise I also *sketched* a more general approach to
  //defunctionalization, based on GADTs. Instead of having different types
  //of functions for each function type (above, FunctionValueIntInt and
  //FunctionValueIntListInt), have one FunctionValue type with type parameters.
  //We won't discuss this in detail, but here's an example for the curious:
  object DefunctionalizedTypeParams {
    sealed trait FunctionValue[Src, Dest]
    //Just a few examples, adding the others should be no problem.
    case class Plus1() extends FunctionValue[Int, Int]
    case class Plus2() extends FunctionValue[Int, Int]
    case class ListF(f: FunctionValue[Int, Int]) extends FunctionValue[Int, List[Int]]

    def apply[A, B](f: FunctionValue[A, B])(x: A): B = f match {
      case Plus1() => x + 1
      case Plus2() => x + 2
      case ListF(f) => List(apply(f)(x))
    }

    //We can keep the old map and flatMap:
    def map(xs: List[Int])(f: FunctionValue[Int, Int]): List[Int] = xs match {
      case Nil => Nil
      case x :: xs => apply(f)(x) :: map(xs)(f)
    }

    def flatMap(xs: List[Int])(f: FunctionValue[Int, List[Int]]): List[Int] = xs match {
      case Nil => Nil
      case x :: xs => apply(f)(x) ++ flatMap(xs)(f)
    }
    def map2(xs: List[Int])(f: FunctionValue[Int, Int]): List[Int] = flatMap(xs)(ListF(f))

    def caller1(l: List[Int]) =
      map(l)(Plus1()) ++
        map(List(1, 2, 3))(Plus2())

    //But now we can also write generic versions of them, by only changing the type
    //signatures:
    def flatMapGen[A, B](xs: List[A])(f: FunctionValue[A, List[B]]): List[B] = xs match {
      case Nil => Nil
      case x :: xs => apply(f)(x) ++ flatMapGen(xs)(f)
    }
  }

  //Task 2
  def f1(l1: Option[Int], l2: Option[Int]): Option[Int] =
    for {
      x <- l1
      y <- l2
    } yield x

  def f2(l1: Option[Int], l2: Option[Int]): Option[(Int, Int)] =
    for {
      x <- l1
      y <- l2
    } yield (x, y)

  //Task 2A-2C: desugar comprehensions and do type inference.
  //I also added the intermediate steps.
  def f1DesugarStep1(l1: Option[Int], l2: Option[Int]): Option[Int] =
    l1.flatMap { x =>
      for {
        y <- l2
      } yield x
    }

  def f1DesugarStep2(l1: Option[Int], l2: Option[Int]): Option[Int] =
    l1.flatMap[Int] { (x: Int) =>
      l2.map[Int]((y: Int) => x)
    }

  def f2DesugarStep1(l1: Option[Int], l2: Option[Int]): Option[(Int, Int)] =
    l1.flatMap { x =>
      for {
        y <- l2
      } yield (x, y)
    }

  def f2DesugarStep2(l1: Option[Int], l2: Option[Int]): Option[(Int, Int)] =
    l1.flatMap[(Int, Int)] { (x: Int) =>
      l2.map[(Int, Int)]((y: Int) => (x, y))
    }
  //Task 2B

  //f1 and lifted functions
  def yToX(x: Int)(y: Int) =
    x

  def xMapYToX(l2: Option[Int])(x: Int) =
    l2.map(yToX(x))

  def f1DesugarStep2LL(l1: Option[Int], l2: Option[Int]): Option[Int] =
    l1.flatMap(xMapYToX(l2))


  //f2 and lifted functions
  def yToXY(x: Int)(y: Int) =
    (x, y)

  def xMapYToXY(l2: Option[Int])(x: Int) =
    l2.map(yToXY(x))

  def f2DesugarStep2LL(l1: Option[Int], l2: Option[Int]): Option[(Int, Int)] =
    l1.flatMap(xMapYToXY(l2))

  //Task 3
  object InlinedInterpreter {
    sealed abstract class Exp
    case class Num(n: Int) extends Exp
    case class Id(name: Symbol) extends Exp
    case class Add(lhs: Exp, rhs: Exp) extends Exp
    type Value = Int
    type Env = Map[Symbol, Value]
    type R = Env

    type M[X] = R => X
    def unit[A](a: A): M[A] =
      r => a
    def bind[A, B](action1: M[A])(action2: A => M[B]): M[B] =
      r => action2(action1(r))(r)
    def bindPrime[A, B] =
      //Fun('action1, Fun('action2, ...))
      (action1: M[A]) =>
        (action2: A => M[B]) =>
          (r: R) => action2(action1(r))(r)
    def ask: M[R] =
      r => r
    def local[A](f: R => R, p: M[A]): M[A] =
      r => p(f(r))

    //This code adds methods map and flatMap on values of type M[A].
    implicit class monadicSyntax[A](p: M[A]) {
      def flatMap[B](f: A => M[B]) = bind(p)(f)
      def map[B](f: A => B) = flatMap(x => unit(f(x)))
    }

    object OriginalInterpreterVersion {
      def eval(e: Exp): M[Value] = e match {
        case Num(n) =>
          unit(n)
        case Id(x) =>
          for {
            env <- ask
          } yield env(x)
        case Add(l, r) =>
          for {
            lV <- eval(l)
            rV <- eval(r)
          } yield lV + rV
      }
    }
    object InterpreterWithDesugaredForComprehensions {
      def eval(e: Exp): M[Value] = e match {
        case Num(n) =>
          unit(n)
        case Id(x) =>
          ask.map { env =>
            env(x)
          }
        case Add(l, r) =>
          //          eval(l).flatMap { lV =>
          //            for {
          //              rV <- eval(r)
          //            } yield lV + rV
          //          }
          eval(l).flatMap { lV =>
            eval(r).map { rV =>
              lV + rV
            }
          }
      }
    }

    object InterpreterWithDesugaredForComprehensionsAndTypeInference {
      def eval(e: Exp): M[Value] = e match {
        case Num(n) =>
          unit[Int](n)
        case Id(x) =>
          ask.map[Int]((env: Env) => env(x))
        case Add(l, r) =>
          //        eval(l).flatMap { lV =>
          //          for {
          //            rV <- eval(r)
          //          } yield lV + rV
          //        }
          eval(l).flatMap[Int] { (lV: Int) =>
            eval(r).map[Int] { (rV: Int) =>
              lV + rV
            }
          }
      }
    }

    object InlineMapFlatMap {
      def eval(e: Exp): M[Value] = e match {
        case Num(n) =>
          unit(n)
        case Id(x) =>
          //First, inline map:
          //ask.flatMap(env => unit(env(x)))
          //Then, inline flatMap:
          bind(ask) { env =>
            unit(env(x))
          }
        case Add(l, r) =>
          //        eval(l).flatMap { lV =>
          //          for {
          //            rV <- eval(r)
          //          } yield lV + rV
          //        }
          bind(eval(l)) { lV =>
            bind(eval(r)) { rV =>
              unit(lV + rV)
            }
          }
      }
    }

    object InlineMapFlatMapAndTypeInference {
      def eval(e: Exp): M[Value] = e match {
        case Num(n) =>
          unit[Int](n)
        case Id(x) =>
          //ask.flatMap(env => unit(env(x)))
          bind[Env, Int](ask) { (env: Env) =>
            unit[Int](env(x))
          }
        case Add(l, r) =>
          bind[Int, Int](eval(l)) { (lV: Int) =>
            bind[Int, Int](eval(r)) { (rV: Int) =>
              unit[Int](lV + rV)
            }
          }
      }
    }

    object InlineBindUnitAsk {
      def eval(e: Exp): M[Value] = e match {
        case Num(n) =>
          r => n
        case Id(x) =>

          /*bind[Env, Int](ask) { (env: Env) =>
            unit[Int](env(x))
          }*/
          /*
          ((action1: M[A]) =>
            (action2: A => M[B]) =>
              (r: R) => action2(action1(r))(r)
          )(ask) { (env: Env) =>
            unit[Int](env(x))
          }
          */
          //          r => ((env: Env) =>
          //            unit[Int](env(x)))(ask(r))(r)

          r =>
            ((env: Env) => (r: Env) => env(x))(
              ((r: Env) => r)(
                r))(
              r)

        case Add(le, re) =>
          (r: R) =>
            ((lV: Int) =>
              (r: R) =>
                ((rV: Int) =>
                  (r: R) =>
                    lV + rV)(
                  eval(re)(r))(
                  r))(
              eval(le)(r))(
              r)
      }
    }

    object FinalVersion {
      def eval(e: Exp): Env => Value = e match {
        case Num(n) =>
          r =>
            n
        case Id(x) =>
          env =>
            env(x)
        case Add(le, re) =>
          /* First two reductions */
//          ((r: R) =>
//            ((lV: Int) =>
//              (r1: R) =>
//                (lV + eval(re)(r)))(eval(le)(r))(r))
          /* Remaining reductions */
//          (r: R) =>
//            eval(le)(r) + eval(re)(r)
          /* After some renaming */
          env =>
            eval(le)(env) + eval(re)(env)
      }
    }
  }
}
