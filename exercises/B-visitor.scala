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

//// It was remarked during exercise session 29.10.2012
//// that the burden of changing existing visitors can
//// be lightened by supplying default arguments to the
//// case class constructor of Visitor.

  id  : Symbol => T
      = (_ : Symbol) => sys.error("Unknown term: Id"),
  wth : (Symbol, T, T) => T
      = (_ : Symbol, _ : T, _ : T) => sys.error("Unknown term: With")
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
  _ * _
)

val print_visitor = new Visitor[String](
  _.toString,
  "( " + _ + " + " + _ + " )",
  "( " + _ + " * " + _ + " )"
)

def eval  : Exp => Int    = fold(eval_visitor)
def print : Exp => String = fold(print_visitor)

/* AE tests

val e = Mul(Add(Num(3), Num(4)), Mul(Num(2), Num(3)))
eval(e)
print(e)

*/

val bound_variables_visitor = new Visitor[Set[Symbol]] (
  _ => Set(),
  _ ++ _,
  _ ++ _,
  _ => Set(),
  (x, bv_in_xdef, bv_in_body) => (bv_in_xdef ++ bv_in_body) + x
)

val free_variables_visitor = new Visitor[Set[Symbol]] (
  _ => Set(),
  _ ++ _,
  _ ++ _,
  Set(_),
  (x, fv_in_xdef, fv_in_body) => fv_in_xdef ++ (fv_in_body - x)
)

def bound_variables : Exp => Set[Symbol] = fold(bound_variables_visitor)
def free_variables  : Exp => Set[Symbol] = fold(free_variables_visitor)

def all_variables(e : Exp) = bound_variables(e) ++ free_variables(e)

/* WAE tests

val e = With('x, With('y, Id('x), Id('y)), Id('z))
bound_variables(e)
free_variables(e)
all_variables(e)

*/

// Trick question to those who attended "compiler construction":
//
// Is it possible to extend eval_visitor to work on WAE terms?
// Why, or why not?
