/*

Programming language and types

Exercise session B on 29.10.2012

Github Animation: visitor vs. pattern matching

Suppose AE expressions with eval and pretty-printing functions are
defined. We want to extend the language to WAE expressions and add
functions to compute all variables occurring in a WAE term, bound
and free.

This file illustrates the pattern-matching method. Browse the commit
history and ask yourself: Is it easier to add a new term or a new
function?

*/

// We do not seal Exp this time because we want to extend it later.
abstract class Exp 
case class Num(n: Int) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp

def eval(e : Exp) : Int = e match {
  case Num(n)        => n
  case Add(lhs, rhs) => eval(lhs) + eval(rhs)
  case Mul(lhs, rhs) => eval(lhs) * eval(rhs)
}

def print(e : Exp) : String = e match {
  case Num(n)        => n.toString
  case Add(lhs, rhs) => "( " + print(lhs) + " + " + print(rhs) + " )"
  case Mul(lhs, rhs) => "( " + print(lhs) + " * " + print(rhs) + " )"
}

/* AE tests

val e = Mul(Add(Num(3), Num(4)), Mul(Num(2), Num(3)))
eval(e)
print(e)

*/

case class Id(x : Symbol) extends Exp
case class With(x : Symbol, xdef : Exp, body : Exp) extends Exp

def bound_variables(e : Exp) : Set[Symbol] = e match {
  case Num(n)        => Set()
  case Add(lhs, rhs) => bound_variables(lhs) ++ bound_variables(rhs)
  case Mul(lhs, rhs) => bound_variables(lhs) ++ bound_variables(rhs)
  case Id(x)         => Set()
  case With(x, d, b) => (bound_variables(d) ++ bound_variables(b)) + x
}

def free_variables(e : Exp) : Set[Symbol] = e match {
  case Num(n)        => Set()
  case Add(lhs, rhs) => free_variables(lhs) ++ free_variables(rhs)
  case Mul(lhs, rhs) => free_variables(lhs) ++ free_variables(rhs)
  case Id(x)         => Set(x)
  case With(x, d, b) => free_variables(d) ++ (free_variables(b) - x)
}

def  all_variables(e : Exp) = free_variables(e) ++ bound_variables(e)

/* WAE tests

val e = With('x, With('y, Id('x), Id('y)), Id('z))
bound_variables(e)
free_variables(e)
all_variables(e)

*/
