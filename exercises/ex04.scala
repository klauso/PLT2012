/*
Programming languages and types

Exercise session D on 12.11.2012

Hand in
   - anytime
   - as a single .scala file
   - by E-Mail to pllecture@informatik

Solution will be posted before 19.11.12, 1000 hrs.

The tutor shall give feedback to each submission, without giving
points. Homework does not count toward course requirement. Do them for
your own benefit.

While everyone should write their own solution, it is recommended to
work face-to-face in small groups.


Contents
========

1. Implementing RCFAE in FAE
*/


/*
1. Implementing RCFAE in FAE
============================

It turns out FAE is so powerful that we can implement Letrec-
expressions as syntactic sugar. Let's have the FAE interpreter in
place first.
*/

abstract class Exp
case class Num(n: Int) extends Exp
case class Id(name: Symbol) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp
case class If0(cond: Exp, thenExp: Exp, elseExp: Exp) extends Exp
implicit def num2exp(n: Int) = Num(n)
implicit def id2exp(s: Symbol) = Id(s)
case class Fun(param: Symbol, body: Exp) extends Exp
case class App (funExpr: Exp, argExpr: Exp) extends Exp

// The syntax sugar `wth` may eventually prove useful.
def wth(x: Symbol, xdef: Exp, body: Exp) : Exp = App(Fun(x,body),xdef)

sealed abstract class Value
type Env = Map[Symbol, Value]
case class NumV(n: Int) extends Value
case class ClosureV(f: Fun, env: Env) extends Value

// The `eval` method is adapted from the evaluator with environments
// in lecture notes. The only change is to handle Mul- and If0-
// expressions, which should contain no surprise.

def eval(e: Exp, env: Env = Map()) : Value = e match {
  case Num(n: Int) => NumV(n)
  case Id(x) => env(x)
  case If0(cond, thenExp, elseExp) => eval(cond,env) match {
    case NumV(0) => eval(thenExp,env)
    case _ => eval(elseExp,env)
  }    
  case Add(l,r) => {
    (eval(l,env), eval(r,env)) match {
      case (NumV(v1),NumV(v2)) => NumV(v1+v2)
      case _ => sys.error("can only add numbers")
    }
  }
  case Mul(l,r) => {
    (eval(l,env), eval(r,env)) match {
      case (NumV(v1),NumV(v2)) => NumV(v1*v2)
      case _ => sys.error("can only multiply numbers")
    }
  }
  case f@Fun(param,body) => ClosureV(f, env)
  case App(f,a) => eval(f,env) match {
    case ClosureV(f,closureEnv)
      => eval(f.body, closureEnv + (f.param -> eval(a,env)))
    case _ => sys.error("can only apply functions")
  }
}


// DEFINITIONS
//
// For brevity, we will use the lambda-calculus syntax when discussing
// FAE terms. We write
//
//     lambda x. body     for     Fun('x, body),
//     exp1 exp2          for     App(exp1, exp2),
//
// and we consider the binding between a function and its (one)
// argument to be tighter than the operators + or *; so for example
// f n + 1 means (f n) + 1.
//
// Suppose f is a Fun-expression and f = (lambda x. body).
// Then f and the term (lambda y. f y) behave identically on all
// arguments as long as y is not free in body. We say that the terms
//
//     f     and     (lambda y. f y)
//
// are eta-equivalent. In addition, two terms are eta-equivalent
// if they have the same constructor and all their subterms are
// eta-equivalent.


// a) Observe the Z-combinator below.
//    Prove that for every Fun-expression f, the value of (Z f) is
//    eta-equivalent to f (Z f).
//
//    If we equate eta-equivalent terms, then what we want to prove
//    can be written as
//
//        Z f == f (Z f).
//
//    That is why Z is called a "fixed-point combinator". More on the
//    topic:
//
//        http://en.wikipedia.org/wiki/Fixed-point_combinator

//    Z = lambda f.
//          (lambda x. f (lambda y. x x y))
//          (lambda x. f (lambda y. x x y))

val Z =
  Fun('f, App(
    Fun( 'x, App('f, Fun('y, App(App('x, 'x), 'y)))),
    Fun( 'x, App('f, Fun('y, App(App('x, 'x), 'y))))
  ))


// b) Prove that if a function f is a fixed point of the higher-order
//    function phi_of_factorial below, then (f n) computes the
//    factorial n. In other words, prove that
//
//        f == phi_of_factorial f
//
//    implies
//
//        f 0 == 1,
//        f n == n * f (n - 1).

//    phi_of_factorial = lambda f.
//                         lambda x. If0(x, 1, x * f(x - 1))

val phi_of_factorial =
  Fun('f, Fun('x, If0('x, 1, Mul('x, App('f, Add('x, -1))))))


// c) Given a) and b), write down the factorial function as a FAE
// term.

// val factorial = ...

// A test. Uncomment to run.

/*
def call_fact(n: Int) : Int = eval(App(factorial, n)) match {
  case NumV(m) => m ; case _ => sys.error("Bug in factorial!")
}
assert(
List(0, 1, 2, 3,  4,   5,   6,    7,     8,      9).map(call_fact) ==
List(1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880))
*/


// d) Write down a FAE term `fib` such that (fib n) computes the nth
//    fibonnacci number.



// A test. Uncomment to run.

/*
def call_fib(n: Int) : Int = eval(App(fib, n)) match {
  case NumV(m) => m ; case _ => sys.error("Bug in fib!")
}
assert(
List(0, 1, 2, 3, 4, 5,  6,  7,  8,  9).map(call_fib) ==
List(1, 1, 2, 3, 5, 8, 13, 21, 34, 55))
*/


// e) Write down letrec as syntactic sugar of FAE.

def letrec(x: Symbol, xdef: Exp, body: Exp) : Exp
  = sys.error("Implement me!")

// A test. Uncomment to run.

/*
val sum = letrec(
  'sum,
  Fun('n, If0('n, 0, Add('n, App('sum, Add('n,-1))))),
  App('sum, 10)
)
assert(eval(sum) == NumV(55))
*/
