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
