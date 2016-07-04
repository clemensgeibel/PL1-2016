// Hindley-Milner type inference with let-polymorphism

sealed abstract class Type
case class FunType(from: Type, to: Type) extends Type
case class NumType() extends Type
case class TypeVar(x: Symbol) extends Type

def freeTypeVars(t: Type) : Set[Symbol] = t match {
  case FunType(f,t) => freeTypeVars(f) ++ freeTypeVars(t)
  case NumType() => Set.empty
  case TypeVar(x) => Set(x)
}

case class Substitution(m: Map[Symbol,Type]) extends Function[Type,Type] {
  def apply(t: Type) = t match {
    case FunType(from,to) => FunType(this(from),this(to))
    case NumType() => NumType()
    case TypeVar(x) => m.getOrElse(x,TypeVar(x))
  }
}

// Robinson unification algorithm

def unify(eq: List[(Type,Type)]) : Type => Type = eq match {
  case Nil => Substitution(Map.empty)
  case (NumType(),NumType()) :: rest => unify(rest)
  case (FunType(f1,t1),FunType(f2,t2)) :: rest => unify((f1,f2) :: (t1,t2) :: rest)
  case (TypeVar(x),TypeVar(y)) :: rest if x == y => unify(rest)
  case (TypeVar(x),t) :: rest => {
    if (freeTypeVars(t)(x)) sys.error(s"Occurs check: $x occurs in $t")
    val s = Substitution(Map(x -> t))
    s.andThen(unify(rest.map(p => (s(p._1),s(p._2)))))
  }
  case (t,TypeVar(x)) :: rest => unify((TypeVar(x),t) :: rest)
  case (t1,t2) :: rest => sys.error(s"Cannot unify $t1 and $t2")
}


sealed abstract class Exp
case class Num(n: Int) extends Exp
case class Id(name: Symbol) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
implicit def num2exp(n: Int) = Num(n)
implicit def id2exp(s: Symbol) = Id(s)
case class Fun(param: Symbol, body: Exp) extends Exp // No type annotation!
case class App (funExpr: Exp, argExpr: Exp) extends Exp
case class Let(x: Symbol, xdef: Exp, body: Exp) extends Exp

def freshName(names: Set[Symbol], default: Symbol) : Symbol = {
  var last : Int = 0
  var freshName = default
  while (names contains freshName) { freshName = Symbol(default.name+last.toString); last += 1; }
  freshName
}

def freeVars(e: Exp) : Set[Symbol] =  e match {
   case Id(x) => Set(x)
   case Add(l,r) => freeVars(l) ++ freeVars(r)
   case Fun(x,body) => freeVars(body) - x
   case App(f,a) => freeVars(f) ++ freeVars(a)
   case Num(n) => Set.empty
   case Let(x,xdef,body) => freeVars(xdef) ++ (freeVars(body) - x)
}

def subst(e1 : Exp, x: Symbol, e2: Exp) : Exp = e1 match {
  case Num(n) => e1
  case Add(l,r) => Add(subst(l,x,e2), subst(r,x,e2))
  case Id(y) => if (x == y) e2 else Id(y)
  case App(f,a) => App(subst(f,x,e2),subst(a,x,e2))
  case Fun(param,body) =>
    if (param == x) e1 else {
      val fvs = freeVars(body) ++ freeVars(e2)
      val newvar = freshName(fvs, param)
      Fun(newvar,subst(subst(body, param, Id(newvar)), x, e2))
    }
  case Let(y,ydef,body) =>
    if (x == y) Let(y,subst(ydef,x,e2),body) else {
      val fvs = freeVars(body) ++ freeVars(e2)
      val newvar = freshName(fvs,y)
      Let(newvar,subst(ydef,x,e2),subst(subst(body,y,Id(newvar)),x,e2))
    }
}

var tyvCount : Int = 0
def freshTypeVar : TypeVar = {
  tyvCount += 1
  TypeVar(Symbol("X"+tyvCount.toString))
}

def typeCheck(e: Exp, gamma: Map[Symbol,Type]) : (List[(Type,Type)],Type) = e match {
  case Num(n) => (List.empty, NumType())
  case Id(x) => gamma.get(x) match {
    case Some(t) => (List.empty, t)
    case _ => sys.error("free variable: " ++ x.toString)
  }
  case Add(l,r) => (typeCheck(l,gamma),typeCheck(r,gamma)) match {
    case ((eq1,t1),(eq2,t2)) => ((t1,NumType()) :: (t2,NumType()) :: (eq1++eq2), NumType())
  }
  case Fun(x,body) => {
    val xtype = freshTypeVar
    val resbody = typeCheck(body, gamma + (x -> xtype))
    (resbody._1,FunType(xtype,resbody._2))
  }
  case App(f,a) => {
    val toType = freshTypeVar
    (typeCheck(f,gamma),typeCheck(a,gamma)) match {
      case ((eqs1,ft),(eqs2,at)) => ((ft,FunType(at,toType)) :: (eqs1++eqs2),toType)
    }
  }
  case Let(x,xdef,body) => typeCheck(subst(body,x,xdef),gamma) // Let-Polymorphism!

}

def doTypeCheck(e: Exp, gamma: Map[Symbol,Type]) = {
  val tc = typeCheck(e,gamma)
  unify(tc._1)(tc._2)
}

def eval(e: Exp) : Exp = e match {
  case Id(v) => sys.error("unbound identifier: " + v.name)
  case Add(l,r) => (eval(l), eval(r)) match {
                     case (Num(x),Num(y)) => Num(x+y)
                     case _ => sys.error("can only add numbers")
                    }
  case App(f,a) => eval(f) match {
     case Fun(x,body) => eval( subst(body,x, eval(a)))  // call-by-value
     case _ => sys.error("can only apply functions")
  }
  case Let(x,xdef,body) => eval(subst(body,x,eval(xdef)))
  case _ => e // numbers and functions evaluate to themselves
}


assert(doTypeCheck(42,Map.empty) == NumType())
assert(doTypeCheck(Fun('x,Add('x,1)),Map.empty) == FunType(NumType(),NumType()))
assert(doTypeCheck(Let('id, Fun('x,'x), App(App('id,Fun('x,Add('x,1))),App('id,42))),Map.empty) == NumType())

// Completeness of type inference:
// If there exist type annotations that make a program type-check in the STLC type checker,
// then the type inference will also be able to type-check the non-annotated version of the program.

// Due to let-polymorphism, this program also type-checks some programs that would be ill-formed in STLC

// The type system is still sound: 
// If doTypeCheck(e,Map.empty) == t, then eval(e) == v and doTypeCheck(v) == t