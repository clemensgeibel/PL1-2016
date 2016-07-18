object Hw05Task2Sol {
  //PG: First, define FAE + Multiplication, just so we can show how to support
  //both for the pretty-printer (not included yet).
  sealed abstract class Exp
  case class Num(n: Int) extends Exp
  case class Id(name: Symbol) extends Exp
  case class Add(lhs: Exp, rhs: Exp) extends Exp
  case class Mul(lhs: Exp, rhs: Exp) extends Exp
  implicit def num2exp(n: Int) = Num(n)
  implicit def id2exp(s: Symbol) = Id(s)

  case class Fun(param: Symbol, body: Exp) extends Exp
  case class App(funExpr: Exp, argExpr: Exp) extends Exp

  def wth(x: Symbol, xdef: Exp, body: Exp): Exp = App(Fun(x, body), xdef)

  def freeVars(e: Exp): Set[Symbol] = e match {
    case Id(x)            => Set(x)
    case Add(l, r)        => freeVars(l) ++ freeVars(r)
    case Mul(l, r)        => freeVars(l) ++ freeVars(r)
    case Fun(x, body)     => freeVars(body) - x
    case App(f, a)        => freeVars(f) ++ freeVars(a)
    case Num(n)           => Set.empty
  }

  sealed abstract class Value
  case class NumV(n: Int) extends Value
  case class BoolV(b: Boolean) extends Value
  case class ClosureV(f: Fun, env: Env) extends Value
  type Env = Map[Symbol, Value]

  def eval(e: Exp, env: Env): Value = e match {
    case Num(n)  => NumV(n)
    case Id(x)   => env(x)
    case Add(l, r) =>
      (eval(l, env), eval(r, env)) match {
        case (NumV(v1), NumV(v2)) => NumV(v1 + v2)
        case _                    => sys.error("can only add numbers")
      }
    case Mul(l, r) =>
      (eval(l, env), eval(r, env)) match {
        case (NumV(v1), NumV(v2)) => NumV(v1 * v2)
        case _                    => sys.error("can only multiply numbers")
      }
    case f @ Fun(param, body) =>
      ClosureV(f, env filterKeys freeVars(f))
    case App(f, a) => eval(f, env) match {
      // Use environment stored in closure to realize proper lexical scoping!
      case ClosureV(f, closureEnv) =>
        eval(f, env) match {
          // Use environment stored in closure to realize proper lexical scoping!
          case ClosureV(f, closureEnv) => eval(f.body, closureEnv + (f.param -> eval(a, env)))
          case _                       => sys.error("can only apply functions")
        }
      case _ => sys.error("can only apply functions")
    }
  }

  def freshName(names: Set[Symbol], default: Symbol): Symbol = {
    var last: Int = 0
    var freshName = default
    while (names contains freshName) { freshName = Symbol(default.name + last.toString); last += 1; }
    freshName
  }

  assert(freshName(Set('y, 'z), 'x) == 'x)
  assert(freshName(Set('x2, 'x0, 'x4, 'x, 'x1), 'x) == 'x3)

  //PG: Standard substitution.
  def subst(e1: Exp, x: Symbol, e2: Exp): Exp = e1 match {
    case Num(n)    => e1
    case Add(l, r) => Add(subst(l, x, e2), subst(r, x, e2))
    case Mul(l, r) => Mul(subst(l, x, e2), subst(r, x, e2))
    case Id(y)     => if (x == y) e2 else Id(y)
    case App(f, a) => App(subst(f, x, e2), subst(a, x, e2))
    case Fun(param, body) =>
      if (param == x) e1 else {
        val fvs = freeVars(body) ++ freeVars(e2) + x
        val newvar = freshName(fvs, param)
        Fun(newvar, subst(subst(body, param, Id(newvar)), x, e2))
      }
  }

  //PG: Substitution, reimplemented using an inner function. This saves a bit of repetition.
  def substV2(x: Symbol, e2: Exp): Exp => Exp = {
    //Defining this go function avoids repeating the map1 and map2 parameters in all recursive subcalls
    def go(e1: Exp): Exp =
      e1 match {
        case Num(n)                 => e1
        case Add(l, r)              => Add(go(l), go(r))
        case Mul(l, r)              => Mul(go(l), go(r))
        case Id(y)                  => if (x == y) e2 else Id(y)
        case App(f, a)              => App(go(f), go(a))
        case Fun(param, body) =>
          if (param == x)
            Fun(param, body)
          else {
            val fvs = freeVars(body) ++ freeVars(e2) + x
            val newvar = freshName(fvs, param)
            Fun(newvar, go(substV2(param, Id(newvar))(body)))
          }
      }
    go
  }

  //TASK 2: Implement syntactic equivalence by hand.
  //This has linear worst-case complexity (precisely, O(max(|e1|, |e2|)), where |e| is the size of e).
  def syntacticEquivalence(e1: Exp, e2: Exp): Boolean = {
    (e1, e2) match {
      case (Num(n1), Num(n2))         => n1 == n2
      case (Add(l1, r1), Add(l2, r2)) => syntacticEquivalence(l1, l2) && syntacticEquivalence(r1, r2)
      case (Mul(l1, r1), Mul(l2, r2)) => syntacticEquivalence(l1, l2) && syntacticEquivalence(r1, r2)

      case (Id(x1), Id(x2))           => x1 == x2
      case (App(f1, a1), App(f2, a2)) => syntacticEquivalence(f1, f2) && syntacticEquivalence(a1, a2)
      case (Fun(p1, body1), Fun(p2, body2)) =>
        p1 == p2 && syntacticEquivalence(body1, body2)
      case (_, _) => false
    }
  }

  //TASK 2: alpha-equivalence, done easily. This is just a variant of syntactic equivalence;
  //we just change the handling of variables in functions.
  //This has quadratic worst-case complexity because of the repeated substitutions.
  def alphaEqSimple(e1: Exp, e2: Exp): Boolean = {
    (e1, e2) match {
      case (Num(n1), Num(n2))               => n1 == n2
      case (Add(l1, r1), Add(l2, r2))       => alphaEqSimple(l1, l2) && alphaEqSimple(r1, r2)
      case (Mul(l1, r1), Mul(l2, r2))       => alphaEqSimple(l1, l2) && alphaEqSimple(r1, r2)

      case (Id(x1), Id(x2))                 => x1 == x2
      case (App(f1, a1), App(f2, a2))       => alphaEqSimple(f1, f2) && alphaEqSimple(a1, a2)
      case (Fun(p1, body1), Fun(p2, body2)) =>
        val names = freeVars(body1) ++ freeVars(body2)
        val fresh: Symbol = freshName(names, p1)
        alphaEqSimple(subst(body1, p1, Id(fresh)), subst(body2, p2, Id(fresh)))
      case (_, _) => false
    }
  }

  //PG: EXTRA: substitute multiple variables at the same time.
  //That's faster than using substitutions repeatedly, and understanding this
  //can help writing the more advanced version of alpha-equivalence below.
  def parallelSubst(replacements: Map[Symbol, Exp]): Exp => Exp = {
    def go(e1: Exp): Exp =
      e1 match {
        case Num(n)                 => e1
        case Add(l, r)              => Add(go(l), go(r))
        case Mul(l, r)              => Mul(go(l), go(r))
        case Id(y)                  => replacements.getOrElse(y, e1)
        case App(f, a)              => App(go(f), go(a))
        case Fun(param, body) =>
          if (replacements contains param)
            Fun(param, body)
          else {
            val fvs = freeVars(body) ++ replacements.values.flatMap(freeVars) ++ replacements.keySet
            val newvar = freshName(fvs, param)
            Fun(newvar, parallelSubst(replacements + (param -> Id(newvar)))(body))
          }
      }
    go
  }

  //TASK 2: alpha-equivalence, more advanced solution.
  //This has linear worst-case complexity because we avoid repeated substitutions.
  def alphaEquiv(map1: Map[Symbol, Symbol], map2: Map[Symbol, Symbol])(l: Exp, r: Exp): Boolean = {
    //Defining this go function avoids repeating the map1 and map2 parameters in all recursive subcalls
    def go(e1: Exp, e2: Exp): Boolean =
      (e1, e2) match {
        case (Num(n1), Num(n2))               => n1 == n2
        case (Add(l1, r1), Add(l2, r2))       => go(l1, l2) && go(r1, r2)
        case (Mul(l1, r1), Mul(l2, r2))       => go(l1, l2) && go(r1, r2)


        case (Id(x1), Id(x2))                 =>
          val bound1 = map1.contains(x1)
          val bound2 = map2.contains(x2)
          bound1 == bound2 && (bound1 && map1(x1) == map2(x2) || x1 == x2)
        case (App(f1, a1), App(f2, a2))       => go(f1, f2) && go(a1, a2)
        case (Fun(p1, body1), Fun(p2, body2)) =>
          val names = map1.keySet ++ map1.values ++ map2.keySet ++ map2.values ++ freeVars(body1) ++ freeVars(body2)
          val fresh: Symbol = freshName(names, p1)
          alphaEquiv(map1 + (p1 -> fresh), map2 + (p2 -> fresh))(body1, body2)
        case (_, _) => false
      }
    go(l, r)
  }


  assert(substV2('x, 7)(Add(5, 'x)) == Add(5, 7))
  assert(substV2('y, 7)(Add(5, 'x)) == Add(5, 'x))
  assert(substV2('x, 7)(Fun('x, Add('x, 'y))) == Fun('x, Add('x, 'y)))
  // test capture-avoiding substitution
  assert(substV2('y, Add('x, 5))(Fun('x, Add('x, 'y))) == Fun('x0, Add(Id('x0), Add(Id('x), Num(5)))))
  assert(substV2('y, Add(Id('x), 5))(Fun('x, Add(Id('x0), Id('y)))) == Fun('x1, Add(Id('x0), Add(Id('x), Num(5)))))
}
