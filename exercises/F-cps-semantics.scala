/**
 * Meaning of CPSVal
 * =================
 *
 * We give the meaning of CPSVal-constructs in terms of FAE,
 * whose semantics is given in turn by a definitional interpreter.
 * Composing the two transformations gives us a trivial interpreter
 * for CPSVal.
 */

sealed abstract class Exp
case class Num(n: Int) extends Exp
case class Id(name: Symbol) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Fun(param: Symbol, body: Exp) extends Exp
case class App (funExpr: Exp, argExpr: Exp) extends Exp
implicit def num2exp(n: Int) = Num(n)
implicit def id2exp(s: Symbol) = Id(s)

sealed abstract class CPSVal
abstract class CPSExp extends CPSVal
case class CPSNum(n: Int) extends CPSVal
case class CPSCont(v: Symbol, body: CPSExp) extends CPSVal
case class CPSFun(x: Symbol, k: Symbol, body: CPSExp) extends CPSVal
case class CPSVar(x: Symbol) extends CPSVal { override def toString = x.toString }
implicit def id2cpsexp(x: Symbol) = CPSVar(x)

case class CPSContApp(k: CPSVal, a: CPSVal) extends CPSExp
case class CPSFunApp(f: CPSVar, a: CPSVar, k: CPSVar) extends CPSExp
case class CPSAdd(l: CPSVar, r: CPSVar) extends CPSExp

def freeVars(e: Exp) : Set[Symbol] =  e match {
   case Id(x) => Set(x)
   case Add(l,r) => freeVars(l) ++ freeVars(r)
   case Fun(x,body) => freeVars(body) - x
   case App(f,a) => freeVars(f) ++ freeVars(a)
   case Num(n) => Set.empty
}
def freshName(names: Set[Symbol], default: Symbol) : Symbol = {
  var last : Int = 0
  var freshName = default  
  while (names contains freshName) { freshName = Symbol(default.name+last.toString); last += 1; }
  freshName
}

def cps(e: Exp) : CPSCont = e match {
   case Add(e1,e2) => {
     val k = freshName(freeVars(e), 'k)
     val lv = freshName(freeVars(e2), 'lv)
     CPSCont(k, CPSContApp(cps(e1),
       CPSCont(lv, CPSContApp(cps(e2),
         CPSCont('rv, CPSContApp(k,CPSAdd('rv, lv))) )) ))
   }
   case Fun(a, body) => {
     val k = freshName(freeVars(e), 'k)
     val dynk = freshName(freeVars(e), 'dynk)
     CPSCont(k, CPSContApp(k, CPSFun(a, dynk, CPSContApp(cps(body), dynk))))
   }
   case App(f,a) => {
     val k = freshName(freeVars(e), 'k)
     val fval = freshName(freeVars(a), 'fval)
     CPSCont(k, CPSContApp(cps(f),
       CPSCont(fval, CPSContApp(cps(a),
         CPSCont('aval, CPSFunApp(fval, 'aval, k)) )) ))
   }
   case Id(x) => {
     val k = freshName(freeVars(e), 'k)
     CPSCont(k, CPSContApp(k, CPSVar(x)))
   }
   case Num(n) => {
     val k = freshName(freeVars(e), 'k)
     CPSCont('k, CPSContApp('k,CPSNum(n)))
   }
}


sealed abstract class Value
type Env = Map[Symbol, Value]
case class NumV(n: Int) extends Value
case class ClosureV(f: Fun, env: Env) extends Value

/**
 * The definitional interpreter for FAE
 */

def evalWithEnv(e: Exp, env: Env) : Value = e match {
  case Num(n: Int) => NumV(n)
  case Id(x) => env(x)
  case Add(l,r) => {
    (evalWithEnv(l,env), evalWithEnv(r,env)) match {
      case (NumV(v1),NumV(v2)) => NumV(v1+v2)
      case _ => sys.error("can only add numbers")
    }
  }
  case f@Fun(param,body) => ClosureV(f, env)
  case App(f,a) => evalWithEnv(f,env) match {
    // Use environment stored in closure to realize proper lexical scoping!
    case ClosureV(f,closureEnv) => evalWithEnv(f.body, closureEnv + (f.param -> evalWithEnv(a,env)))
    case _ => sys.error("can only apply functions")
  }
}

def eval(e: Exp) = evalWithEnv(e, Map())

/**
 * The function `uncps` explains the meaning of each CPSVal in terms
 * of FAE.
 */

def uncps(c: CPSVal) : Exp = c match {
  case CPSNum(n)
    => Num(n)
  case CPSCont(v: Symbol, body: CPSExp)
    => Fun(v, uncps(body))
  case CPSFun(x: Symbol, k: Symbol, body: CPSExp)
    => Fun(x, Fun(k, uncps(body)))
  case CPSVar(x)
    => Id(x)
  case CPSContApp(k: CPSVal, a: CPSVal)
    => App(uncps(k), uncps(a))
  case CPSFunApp(f: CPSVar, a: CPSVar, k: CPSVar)
    => App(App(f.x, a.x), k.x)
  case CPSAdd(l: CPSVar, r: CPSVar)
    => Add(l.x, r.x)
}

def cps2exp(c: CPSCont) = App(uncps(c), Fun('x, 'x))

/**
 * The trivial interpreter for CPS-transformed FAE terms.
 *
 * Why is the argument type `CPSCont` instead of `CPSVal`?
 */

def starteval(c: CPSCont) = eval( cps2exp(c) )

def wth(x: Symbol, xdef: Exp, body: Exp) : Exp = App(Fun(x,body),xdef)

val test1 = App( Fun('x,Add('x,5)), 7)
val test2 = wth('x, 5, App(Fun('f, App('f,3)), Fun('y,Add('x,'y))))

// The nonterminating redex
val omega = App( Fun('x, App('x, 'x)),
                 Fun('x, App('x, 'x)) )


