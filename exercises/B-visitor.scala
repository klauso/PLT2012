/*

Programming language and types

Exercise session B on 29.10.2012

Github Animation: visitor vs. pattern matching

Suppose AE expressions with eval and pretty-printing functions are
defined. We want to extend the language to WAE expressions and add
functions to compute all variables occurring in a WAE term, bound
and free.

This file illustrates the visitor method. Browse the commit history
and ask yourself: Is it easier to add a new term or a new function?

*/

// We do not seal Exp this time because we want to extend it later.
abstract class Exp 
case class Num(n: Int) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp

case class Id(x : Symbol) extends Exp
case class With(x : Symbol, xdef : Exp, body : Exp) extends Exp

case class Visitor[T](
  num : Int => T,
  add : (T, T) => T,
  mul : (T, T) => T,
  id  : Symbol => T,
  wth : (Symbol, T, T) => T
)

def fold[T](v : Visitor[T])(e : Exp) : T = e match {
  case Num(n)        => v.num(n)
  case Add(lhs, rhs) => v.add(fold(v)(lhs), fold(v)(rhs))
  case Mul(lhs, rhs) => v.mul(fold(v)(lhs), fold(v)(rhs))
  case Id(x)         => v.id(x)
  case With(x, d, b) => v.wth(x, fold(v)(d), fold(v)(b))
}

val eval_visitor = new Visitor[Int](
  identity,
  _ + _,
  _ * _,
  _ => sys.error("Unknown term"),
  (_,_,_) => sys.error("Unknown term")
)

val print_visitor = new Visitor[String](
  _.toString,
  "( " + _ + " + " + _ + " )",
  "( " + _ + " * " + _ + " )",
  _ => sys.error("Unknown term"),
  (_,_,_) => sys.error("Unknown term")
)

def eval  : Exp => Int    = fold(eval_visitor)
def print : Exp => String = fold(print_visitor)

/* AE tests

val e = Mul(Add(Num(3), Num(4)), Mul(Num(2), Num(3)))
eval(e)
print(e)

*/
