/*
Programming Languages and Types.

Exercise session F on 26.11.2012

Hand in
   - anytime
   - as a single .scala file
   - by E-Mail to pllecture@informatik


Solution will be posted before 03.12.12, 1000 hrs.

The tutor shall give feedback to each submission, without giving
points. Homework does not count toward course requirement. Do them for
your own benefit.

While everyone should write their own solution, it is recommended to
work face-to-face in small groups.


Evaluating CPS-transformed FAE
==============================

The lecture script `14-cpstransformation2.scala` demonstrates an
automatic transformation of FAE-terms into continuation-passing-style,
without an evaluator for the resulting code. Please write an eval-
function for `CPSVal`.


Hints

1. If in doubt of the meaning of a CPS-expression, consult the
   additional material `F-cps-semantics.scala`.

2. Tail-call optimisation is encouraged. Tail-call optimisation that
   does not depend on Scala's tail-recursion optimisation would be
   best.


Historical reading on expressivity and optimisation of tail-calls

   http://repository.readscheme.org/ftp/papers/ai-lab-pubs/AIM-443.pdf

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

// Fischer CPS-transformation per lecture notes

def cps(e: Exp) : CPSCont = e match {
   case Add(e1,e2) => {
     val k = freshName(freeVars(e), 'k)
     val lv = freshName(freeVars(e2), 'lv)
     CPSCont(k, CPSContApp(cps(e1),CPSCont(lv, CPSContApp(cps(e2), CPSCont('rv, CPSContApp(k,CPSAdd('rv, lv)))))))
   }  
   case Fun(a, body) => {
     val k = freshName(freeVars(e), 'k)
     val dynk = freshName(freeVars(e), 'dynk)
     CPSCont(k, CPSContApp(k, CPSFun(a, dynk, CPSContApp(cps(body), dynk))))
   }
   case App(f,a) => {
     val k = freshName(freeVars(e), 'k)
     val fval = freshName(freeVars(a), 'fval)
     CPSCont(k, CPSContApp(cps(f), CPSCont(fval, CPSContApp(cps(a), CPSCont('aval, CPSFunApp(fval, 'aval, k))))))
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


// The `starteval` function should be able to compute the value of
// CPS-transformed FAE terms directly. What should be its argument
// type?

// def starteval( ... ) : Value = ...


// Simple test cases. Uncomment to run.

def wth(x: Symbol, xdef: Exp, body: Exp) : Exp = App(Fun(x,body),xdef)

val test1 = App( Fun('x,Add('x,5)), 7)
val test2 = wth('x, 5, App(Fun('f, App('f,3)), Fun('y,Add('x,'y))))

// assert(starteval( cps(test1) ) == NumV(12))
// assert(starteval( cps(test2) ) == NumV(8))
