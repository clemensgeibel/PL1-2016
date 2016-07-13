object Hw10Sol {
  //TASK 3
  object STLCWithTuplesRecords {
    sealed abstract class Type

    sealed abstract class Exp
    case class Num(n: Int) extends Exp
    case class Id(name: Symbol) extends Exp
    case class Add(lhs: Exp, rhs: Exp) extends Exp
    implicit def num2exp(n: Int) = Num(n)
    implicit def id2exp(s: Symbol) = Id(s)
    case class Fun(param: Symbol, t: Type, body: Exp) extends Exp
    case class App(funExpr: Exp, argExpr: Exp) extends Exp
    case class Junit() extends Exp
    case class Let(x: Symbol, xdef: Exp, body: Exp) extends Exp
    case class TypeAscription(e: Exp, t: Type) extends Exp

    case class Product(e1: Exp, e2: Exp) extends Exp
    case class Fst(e: Exp) extends Exp
    case class Snd(e: Exp) extends Exp

    //PG: tuples
    case class Tuple(els: List[Exp]) extends Exp
    case class Proj(e: Exp, i: Int) extends Exp

    case class SumLeft(left: Exp, right: Type) extends Exp
    case class SumRight(left: Type, right: Exp) extends Exp
    case class EliminateSum(e: Exp, fl: Exp, fr: Exp) extends Exp

    def freshName(names: Set[Symbol], default: Symbol): Symbol = {
      var last: Int = 0
      var freshName = default
      while (names contains freshName) { freshName = Symbol(default.name + last.toString); last += 1; }
      freshName
    }

    def freeVars(e: Exp): Set[Symbol] = e match {
      case Id(x)                   => Set(x)
      case Add(l, r)               => freeVars(l) ++ freeVars(r)
      case Fun(x, _, body)         => freeVars(body) - x
      case App(f, a)               => freeVars(f) ++ freeVars(a)
      case Num(n)                  => Set.empty
      case Junit()                 => Set.empty
      case TypeAscription(e, t)    => freeVars(e)
      case Let(x, xdef, body)      => freeVars(xdef) ++ (freeVars(body) - x)
      case Product(e1, e2)         => freeVars(e1) ++ freeVars(e2)
      case Fst(e)                  => freeVars(e)
      case Snd(e)                  => freeVars(e)
      case SumLeft(e, _)           => freeVars(e)
      case SumRight(_, e)          => freeVars(e)
      case EliminateSum(e, fl, fr) => freeVars(e) ++ freeVars(fl) ++ freeVars(fr)
      //PG: tuples
      case Tuple(els)              => els.toSet.flatMap(freeVars)
      case Proj(e, _)              => freeVars(e)
    }

    def subst(e1: Exp, x: Symbol, e2: Exp): Exp = e1 match {
      case Num(n)               => e1
      case Junit()              => e1
      case Add(l, r)            => Add(subst(l, x, e2), subst(r, x, e2))
      case Id(y)                => if (x == y) e2 else Id(y)
      case App(f, a)            => App(subst(f, x, e2), subst(a, x, e2))
      case TypeAscription(e, t) => TypeAscription(subst(e, x, e2), t)
      case Fun(param, t, body) =>
        if (param == x) e1 else {
          val fvs = freeVars(body) ++ freeVars(e2)
          val newvar = freshName(fvs, param)
          Fun(newvar, t, subst(subst(body, param, Id(newvar)), x, e2))
        }
      case Let(y, ydef, body) =>
        if (x == y) Let(y, subst(ydef, x, e2), body) else {
          val fvs = freeVars(body) ++ freeVars(e2)
          val newvar = freshName(fvs, y)
          Let(newvar, subst(ydef, x, e2), subst(subst(body, y, Id(newvar)), x, e2))
        }
      case Product(a, b)           => Product(subst(a, x, e2), subst(b, x, e2))
      case Fst(e)                  => Fst(subst(e, x, e2))
      case Snd(e)                  => Snd(subst(e, x, e2))
      case SumLeft(e, t)           => SumLeft(subst(e, x, e2), t)
      case SumRight(t, e)          => SumRight(t, subst(e, x, e2))
      case EliminateSum(e, fl, fr) => EliminateSum(subst(e, x, e2), subst(fl, x, e2), subst(fr, x, e2))
      //PG: tuples
      case Tuple(els)              => Tuple(els.map(subst(_, x, e2)))
      case Proj(e, i)              => Proj(subst(e, x, e2), i)
    }

    def eval(e: Exp): Exp = e match {
      case Id(v) => sys.error("unbound identifier: " + v.name)
      case Add(l, r) => (eval(l), eval(r)) match {
        case (Num(x), Num(y)) => Num(x + y)
        case _                => sys.error("can only add numbers")
      }
      case App(f, a) => eval(f) match {
        case Fun(x, _, body) => eval(subst(body, x, eval(a))) // call-by-value
        case _               => sys.error("can only apply functions")
      }
      case TypeAscription(e, _) => eval(e)
      case Let(x, xdef, body)   => eval(subst(body, x, eval(xdef)))
      case Product(a, b)        => Product(eval(a), eval(b))
      case Fst(e) => eval(e) match {
        case Product(a, b) => a
        case _             => sys.error("can only apply Fst to products")
      }
      case Snd(e) => eval(e) match {
        case Product(a, b) => b
        case _             => sys.error("can only apply Snd to products")
      }
      case SumLeft(e, t)  => SumLeft(eval(e), t)
      case SumRight(t, e) => SumRight(t, eval(e))
      case EliminateSum(e, fl, fr) => eval(e) match {
        case SumLeft(e2, _)  => eval(App(fl, e2))
        case SumRight(_, e2) => eval(App(fr, e2))
        case _               => sys.error("can only eliminate sums")
      }
      //PG: tuples
      case Tuple(els) => Tuple(els.map(eval))
      case Proj(e, i) => eval(e) match {
        case Tuple(els) => els(i)
        case _          => sys.error("can only project out of tuples")
      }
      case _ => e // numbers and functions evaluate to themselves
    }

    /**
      * We classify values into three types: Booleans, integers, and function types. For function types, we need some abstraction for its input and output; otherwise the type checker cannot be compositional. Luckily we do already have such an abstraction, namely types. Hence ``Funtype`` becomes a recursive data type.
      */

    case class NumType() extends Type
    case class FunType(from: Type, to: Type) extends Type
    case class JunitType() extends Type
    case class ProductType(fst: Type, snd: Type) extends Type
    case class TupleType(elTypes: List[Type]) extends Type

    case class SumType(left: Type, right: Type) extends Type

    /**
      * The type checker for the so-called _Simply-Typed Lambda Calculus_  (STLC). To deal with identifiers, we need an abstraction of environments.  A type environment has the form ``Map[Symbol,Type]``.
      *
      * The type checker for the STLC is as follows:
      */

    def typeCheck(e: Exp, gamma: Map[Symbol, Type]): Type = e match {
      case Num(n)  => NumType()
      case Junit() => JunitType()
      case Id(x) => gamma.get(x) match {
        case Some(t) => t
        case _       => sys.error("free variable: " ++ x.toString)
      }
      case Add(l, r) => (typeCheck(l, gamma), typeCheck(r, gamma)) match {
        case (NumType(), NumType()) => NumType()
        case _                      => sys.error("Type error in Add")
      }
      case Fun(x, t, body) => FunType(t, typeCheck(body, gamma + (x -> t)))
      case App(f, a) => {
        typeCheck(f, gamma) match {
          case FunType(from, to) => if (from == typeCheck(a, gamma)) to else sys.error("type error: arg does not match expected type")
          case _                 => sys.error("first operand of app must be a function")
        }
      }
      case Let(x, xdef, body)   => typeCheck(body, gamma + (x -> typeCheck(xdef, gamma)))
      case TypeAscription(e, t) => if (typeCheck(e, gamma) == t) t else sys.error("type error in ascription")
      case Product(e1, e2)      => ProductType(typeCheck(e1, gamma), typeCheck(e2, gamma))
      case Tuple(els)           => TupleType(els.map(typeCheck(_, gamma)))
      case Proj(e, i) => typeCheck(e, gamma) match {
        case TupleType(elTs) => elTs(i)
        case _               => sys.error("can only project with Proj out of Tuples")
      }
      case Fst(e) => typeCheck(e, gamma) match {
        case ProductType(t1, t2) => t1
        case _                   => sys.error("can only project Products")
      }
      case Snd(e) => typeCheck(e, gamma) match {
        case ProductType(t1, t2) => t2
        case _                   => sys.error("can only project Products")
      }
      case SumLeft(e, t)  => SumType(typeCheck(e, gamma), t)
      case SumRight(t, e) => SumType(t, typeCheck(e, gamma))
      case EliminateSum(e, fl, fr) => typeCheck(e, gamma) match {
        case SumType(left, right) => (typeCheck(fl, gamma), typeCheck(fr, gamma)) match {
          case (FunType(left, t1), FunType(right, t2)) =>
            if (t1 == t2) t1 else sys.error("type error: functions must have same return type")
          case _ => sys.error("type error in EliminateSum: second and third argument must be functions")
        }
        case _ => sys.error("type error: can only eliminate sums")
      }

    }

    //TASK 1
    val boolT = SumType(JunitType(), JunitType())
    //This type is isomorphic to Boolean because, like Boolean, it has two
    //values, that are:
    val v1 = SumLeft(Junit(), JunitType())
    val v2 = SumRight(JunitType(), Junit())
    //so we can create a computable isomorphism (that is, an invertible
    //mapping) by mapping v1 to true and v2 to false.
    //Then, we can translate programs on booleans to programs on boolT using
    //this mapping consistently: everywhere we use true, we change the
    //program to use v1, and translate the boolean primitives this way.
    //
    //There's also another isomorphism mapping v1 to false and v2 to true; we
    //need to pick one isomorphism and use it consistently, but which we pick is
    //just a matter of convention.

    //corresponding to:
    val v1Scala: Either[Unit, Unit] = Left(())
    val v2Scala: Either[Unit, Unit] = Right(())


    //TASK 2
    //Typecheck by hand the following STLC expressions.

    //PG: Testing utility.
    def assertType(e: Exp, tExpected: Type, ctx: Map[Symbol, Type] = Map.empty) = {
      val tActual = typeCheck(e, ctx)
      if (tActual != tExpected) {
        Console.err.println(s"${Console.RED}Expression $e had type $tActual instead of $tExpected.${Console.RESET}")
      } else {
        Console.println(s"${Console.BLUE}Expression $e had type $tActual as expected.${Console.RESET}")
      }
    }

    val plusOneOpen: Exp = Add('x, 1)
    //In the following context:
    val plusOneOpenCtx: Map[Symbol, Type] = Map('x -> NumType())
    def plusOneOpenScala(x: Int) = x + 1
    //I've written down object-level types as meta-level values with names ending
    //in Type.
    val plusOneOpenType = NumType()
    assertType(plusOneOpen, plusOneOpenType, plusOneOpenCtx)

    val e1: Exp = Fun('x, NumType(), 'x)
    val e1Scala = (x: Int) => x
    val e1Type = FunType(NumType(), NumType())
    assertType(e1, e1Type)

    val e2: Exp = Fun('x, boolT, 'x)
    val e2Scala = (x: Boolean) => x
    val e2Type = FunType(boolT, boolT)
    assertType(e2, e2Type)

    val e3: Exp = Fun('x, FunType(NumType(), NumType()), 'x)
    val e3Scala = (x: (Int => Int)) => x
    val e3Type = FunType(FunType(NumType(), NumType()), FunType(NumType(), NumType()))
    assertType(e3, e3Type)

    val apply: Exp = Fun('f, FunType(NumType(), NumType()), Fun('x, NumType(), App('f, 'x)))
    val applyScala = (f: Int => Int) => (x: Int) => f(x)
    val applyType = FunType(FunType(NumType(), NumType()), FunType(NumType(), NumType()))

    val applyNum: Exp = Fun('f, NumType(), Fun('x, NumType(), App('f, 'x)))
    //val applyNumScala = (f: Int) => (x: Int) => f(x)
    //PG: Type error: 'f can't be applied because it does not have a function type.

    val plusOne: Exp = Fun('x, NumType(), Add('x, 1))
    val plusOneScala = (x: Int) => x + 1
    val plusOneType = FunType(NumType(), NumType())

    val appFTo42: Exp = Fun('f, FunType(NumType(), NumType()), App('f, 42))
    val appFTo42Scala = (f: Int => Int) => f(42)
    val appFTo42Type = FunType(FunType(NumType(), NumType()), NumType())

    val funPlusOne: Exp = Fun('x, FunType(NumType(), NumType()), Add('x, 1))
    //val funPlusOneScala = (x: (Int => Int)) => x + 1
    //PG: Type error: Add can't be applied to 'x because 'x does not have a numeric type.

    val e8: Exp = Fun('x, ProductType(NumType(), boolT), SumLeft(Fst('x), boolT))
    val e8Scala = (x: (Int, Boolean)) => Left(x._1)
    val e8Type = FunType(ProductType(NumType(), boolT), SumType(NumType(), boolT))
    assertType(e8, e8Type)

    val e9: Exp = Fun('x, SumType(NumType(), FunType(NumType(), NumType())),
      EliminateSum('x,
        Fun('x, NumType(), Add('x, 1)),
        Fun('f, FunType(NumType(), NumType()), App('f, 42))))

    val e9Scala = (x: Either[Int, Int => Int]) => x match {
      case Left(x)  => x + 1
      case Right(f) => f(42)
    }

    val e9Type = FunType(SumType(NumType(), FunType(NumType(), NumType())), NumType())
    assertType(e9, e9Type)

    val e10: Exp = Fun('x, SumType(NumType(), FunType(NumType(), NumType())),
      EliminateSum('x,
        Fun('x, NumType(), Add('x, 1)),
        Fun('f, FunType(NumType(), NumType()), 'f)))
    //Type error, because the branches return different types,
    //NumType() and FunType(NumType(), NumType()).

    val e10Scala = (x: Either[Int, Int => Int]) => x match {
      case Left(x)  => x + 1
      case Right(f) => f
    }
    //Scala infers here type Either[Int,Int => Int] => Any, where Any is a
    //"universal" type (a bit like Object in Java); both branches are given type
    //Any hence match. This is not possible in STLC.

    //TASK 4, part 1
    /*
    val exTypeInferenceSTLC =
      Let('f, Fun('x, ???, 'x),
        Let('dummy, App('f, 1),
          App('f, Fun('y, NumType(), 'y))))
    */
    //PG: no solution exists, because 'f is used on arguments of different
    //types so no type argument would work.
  }

  //TASK 6
  object HindleyMilner {
    sealed abstract class Type
    case class FunType(from: Type, to: Type) extends Type
    case class NumType() extends Type
    case class TypeVar(x: Symbol) extends Type
    //PG added for products, together with all branches handling this:
    case class ProductType(fst: Type, snd: Type) extends Type

    def freeTypeVars(t: Type): Set[Symbol] = t match {
      case FunType(f, t)     => freeTypeVars(f) ++ freeTypeVars(t)
      case NumType()         => Set.empty
      case TypeVar(x)        => Set(x)
      case ProductType(l, r) => freeTypeVars(l) ++ freeTypeVars(r)
    }

    def substitution(x: Symbol, s: Type) = new Function[Type, Type] {
      def apply(t: Type) = t match {
        case FunType(from, to) => FunType(this(from), this(to))
        case NumType()         => NumType()
        case TypeVar(y)        => if (x == y) s else TypeVar(y)
        case ProductType(l, r) => ProductType(this(l), this(r))
      }
    }

    // Robinson unification algorithm

    def unify(eq: List[(Type, Type)]): Type => Type = eq match {
      case Nil                            => identity _
      case (NumType(), NumType()) :: rest => unify(rest)
      case (ProductType(l1, r1), ProductType(l2, r2)) :: rest =>
        unify((l1, l2) :: (r1, r2) :: rest)
      case (FunType(f1, t1), FunType(f2, t2)) :: rest => unify((f1, f2) :: (t1, t2) :: rest)
      case (TypeVar(x), TypeVar(y)) :: rest if x == y => unify(rest)
      case (TypeVar(x), t) :: rest => {
        if (freeTypeVars(t)(x)) sys.error(s"Occurs check: $x occurs in $t")
        val s = substitution(x, t)
        s.andThen(unify(rest.map(p => (s(p._1), s(p._2)))))
      }
      case (t, TypeVar(x)) :: rest => unify((TypeVar(x), t) :: rest)
      case (t1, t2) :: rest        => sys.error(s"Cannot unify $t1 and $t2")
    }

    import scala.collection.mutable
    //Check two types are equivalent.
    //This is similar
    def compareTypes(a: Type, b: Type,
                     mapA: mutable.Map[Symbol, Symbol] = mutable.Map.empty,
                     mapB: mutable.Map[Symbol, Symbol] = mutable.Map.empty): Boolean =
      (a, b) match {
        case (NumType(), NumType()) => true
        case (TypeVar(vA), TypeVar(vB)) =>
          if (mapA.contains(vA) && mapB.contains(vB)) {
            mapA(vA) == mapB(vB)
          } else if (!mapA.contains(vA) && !mapB.contains(vB)) {
            val newTVar = freshTypeVar()
            mapA += (vA -> newTVar.x)
            mapB += (vB -> newTVar.x)
            true
          } else {
            false
          }
        case (ProductType(l1, r1), ProductType(l2, r2)) =>
          compareTypes(l1, l2, mapA, mapB) &&
            compareTypes(r1, r2, mapA, mapB)
        case (FunType(f1, t1), FunType(f2, t2)) =>
          compareTypes(f1, f2, mapA, mapB) &&
            compareTypes(t1, t2, mapA, mapB)
        case _ => false
      }

    sealed abstract class Exp
    case class Num(n: Int) extends Exp
    case class Id(name: Symbol) extends Exp
    case class Add(lhs: Exp, rhs: Exp) extends Exp
    implicit def num2exp(n: Int) = Num(n)
    implicit def id2exp(s: Symbol) = Id(s)
    case class Fun(param: Symbol, body: Exp) extends Exp // No type annotation!
    case class App(funExpr: Exp, argExpr: Exp) extends Exp
    case class Let(x: Symbol, xdef: Exp, body: Exp) extends Exp
    //PG added for products, together with all branches handling these:
    case class Product(e1: Exp, e2: Exp) extends Exp
    case class Fst(e: Exp) extends Exp
    case class Snd(e: Exp) extends Exp

    def freshName(names: Set[Symbol], default: Symbol): Symbol = {
      var last: Int = 0
      var freshName = default
      while (names contains freshName) { freshName = Symbol(default.name + last.toString); last += 1; }
      freshName
    }

    def freeVars(e: Exp): Set[Symbol] = e match {
      case Id(x)              => Set(x)
      case Add(l, r)          => freeVars(l) ++ freeVars(r)
      case Fun(x, body)       => freeVars(body) - x
      case App(f, a)          => freeVars(f) ++ freeVars(a)
      case Num(n)             => Set.empty
      case Let(x, xdef, body) => freeVars(xdef) ++ (freeVars(body) - x)
      case Product(e1, e2)    => freeVars(e1) ++ freeVars(e2)
      case Fst(e)             => freeVars(e)
      case Snd(e)             => freeVars(e)
    }

    def subst(e1: Exp, x: Symbol, e2: Exp): Exp = e1 match {
      case Num(n)        => e1
      case Add(l, r)     => Add(subst(l, x, e2), subst(r, x, e2))
      case Id(y)         => if (x == y) e2 else Id(y)
      case App(f, a)     => App(subst(f, x, e2), subst(a, x, e2))
      case Product(a, b) => Product(subst(a, x, e2), subst(b, x, e2))
      case Fst(e)        => Fst(subst(e, x, e2))
      case Snd(e)        => Snd(subst(e, x, e2))
      case Fun(param, body) =>
        if (param == x) e1 else {
          val fvs = freeVars(body) ++ freeVars(e2)
          val newvar = freshName(fvs, param)
          Fun(newvar, subst(subst(body, param, Id(newvar)), x, e2))
        }
      case Let(y, ydef, body) =>
        if (x == y) Let(y, subst(ydef, x, e2), body) else {
          val fvs = freeVars(body) ++ freeVars(e2)
          val newvar = freshName(fvs, y)
          Let(newvar, subst(ydef, x, e2), subst(subst(body, y, Id(newvar)), x, e2))
        }
    }

    var tyvCount: Int = 0
    def freshTypeVar(): TypeVar = {
      tyvCount += 1
      TypeVar(Symbol("X" + tyvCount.toString))
    }

    def typeCheck(e: Exp, gamma: Map[Symbol, Type]): (List[(Type, Type)], Type) = e match {
      case Num(n) => (List.empty, NumType())
      case Id(x) => gamma.get(x) match {
        case Some(t) => (List.empty, t)
        case _       => sys.error("free variable: " ++ x.toString)
      }
      case Add(l, r) => (typeCheck(l, gamma), typeCheck(r, gamma)) match {
        case ((eq1, t1), (eq2, t2)) => ((t1, NumType()) :: (t2, NumType()) :: (eq1 ++ eq2), NumType())
      }
      case Fun(x, body) => {
        val xtype = freshTypeVar
        val resbody = typeCheck(body, gamma + (x -> xtype))
        (resbody._1, FunType(xtype, resbody._2))
      }
      case App(f, a) => {
        val toType = freshTypeVar
        (typeCheck(f, gamma), typeCheck(a, gamma)) match {
          case ((eqs1, ft), (eqs2, at)) => ((ft, FunType(at, toType)) :: (eqs1 ++ eqs2), toType)
        }
      }
      case Let(x, xdef, body) => {
        val (constraints1, _) = typeCheck(xdef, gamma) // important if x is not used in body
        val (constraints2, typ) = typeCheck(subst(body, x, xdef), gamma) // Let-Polymorphism!
        (constraints1 ++ constraints2, typ)
      }
      //PG: the core of the solution.
      case Product(l, r) =>
        val (csL, tL) = typeCheck(l, gamma)
        val (csR, tR) = typeCheck(r, gamma)
        (csL ++ csR, ProductType(tL, tR))
      case Fst(e) =>
        val (cs, eType) = typeCheck(e, gamma)
        //PG: here, critically, we don't force eType to be a ProductType itself,
        //because it could be a type variable. Instead, we simply unify it with
        //a type variable.
        val tL = freshTypeVar()
        val tR = freshTypeVar()
        ((ProductType(tL, tR), eType) :: cs,
          tL)
      case Snd(e) =>
        val (cs, eType) = typeCheck(e, gamma)
        //PG: same notes as for Fst.
        val tL = freshTypeVar()
        val tR = freshTypeVar()
        ((ProductType(tL, tR), eType) :: cs,
          tR)
    }

    def doTypeCheck(e: Exp, gamma: Map[Symbol, Type] = Map.empty) = {
      val (constraints, resType) = typeCheck(e, gamma)
      unify(constraints)(resType)
    }

    def eval(e: Exp): Exp = e match {
      case Id(v) => sys.error("unbound identifier: " + v.name)
      case Add(l, r) => (eval(l), eval(r)) match {
        case (Num(x), Num(y)) => Num(x + y)
        case _                => sys.error("can only add numbers")
      }
      case App(f, a) => eval(f) match {
        case Fun(x, body) => eval(subst(body, x, eval(a))) // call-by-value
        case _            => sys.error("can only apply functions")
      }
      case Let(x, xdef, body) => eval(subst(body, x, eval(xdef)))
      case Product(l, r)      => Product(eval(l), eval(r))
      case Fst(e) =>
        eval(e) match {
          case Product(l, r) => l
          case _             => sys.error("Can only project out of pairs")
        }
      case Snd(e) =>
        eval(e) match {
          case Product(l, r) => r
          case _             => sys.error("Can only project out of pairs")
        }
      case _ => e // numbers and functions evaluate to themselves
    }
    //Task 6
    doTypeCheck(Fun('x, Fun('y, Product('x, 'y))), Map.empty)
    doTypeCheck(Fun('x, Fun('y, Fst(Product('x, 'y)))), Map.empty)
    doTypeCheck(Fun('x, Fun('y, Snd(Product('x, 'y)))), Map.empty)
    doTypeCheck(Fun('x, Fst('x)), Map.empty)
    doTypeCheck(Fun('x, Snd('x)), Map.empty)

    //Task 4
    val exTypeInferenceHM =
      Let('f, Fun('x, 'x),
        Let('dummy, App('f, 1),
          App('f, Fun('y, 'y))))
    //PG: Here 'f can have type FunctionType(TypeVar('X), TypeVar('X))

    //Task 5
    def assertType(e: Exp, tExpected: Type, ctx: Map[Symbol, Type] = Map.empty) = {
      val tActual = doTypeCheck(e, ctx)
      if (!compareTypes(tActual, tExpected)) {
        Console.err.println(s"${Console.RED}Expression $e had type $tActual instead of $tExpected.${Console.RESET}")
      } else {
        Console.println(s"${Console.BLUE}Expression $e had type $tActual as expected.${Console.RESET}")
      }
    }

    val e1 = Fun('x, 'x)
    val e1Type = FunType(TypeVar('A), TypeVar('A))
    assertType(e1, e1Type)
    val e2 = Fun('x, Add('x, 1))
    val e2Type = FunType(NumType(), NumType())
    assertType(e2, e2Type)

    val e3: Exp = Add('x, 1)
    val e3Ctx = Map('x -> freshTypeVar)
    //doTypeCheck(e3, e3Ctx) gives:
    val e3Type = NumType()
    assert(doTypeCheck(e3, e3Ctx) == e3Type)
    assertType(e3, e3Type, e3Ctx)

    val apply: Exp = Fun('f, Fun('x, App('f, 'x)))
    val applyType = FunType(FunType(TypeVar('A), TypeVar('B)), FunType(TypeVar('A), TypeVar('B)))
    assertType(apply, applyType)

    val compose: Exp = Fun('f, Fun('g, Fun('x, App('g, App('f, 'x)))))
    //(A => B) => (B => C) => (A => C)
    val composeType =
      FunType(FunType(TypeVar('A), TypeVar('B)),
        FunType(FunType(TypeVar('B), TypeVar('C)),
          FunType(TypeVar('A), TypeVar('C))))
    assertType(compose, composeType)
  }
}

//Run all assertions.
object Hw10App extends App {
  import Hw10Sol._
  STLCWithTuplesRecords
  HindleyMilner
}
//import Hw10Sol._
//import STLCWithTuplesRecords._
//import HindleyMilner._
