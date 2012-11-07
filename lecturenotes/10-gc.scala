/*
These are lecture notes for the "Programming Languages and Types"
course by Klaus Ostermann at the University of Marburg

loosely based on Sec. 13 of "Programming Languages: Application and
Interpretation" by Shriram Krishnamurthi

Please comment/correct/improve these notes via github. Proposals or
questions can be submitted as an "issue"; proposals for
corrections/extensions/improvements can be submitted as a "pull
request". You can of course also send an email to Klaus Ostermann */

/* Let us now consider a more accurate modeling of garbage collection
 * (gc). This time, we will use a mutable store instead of a
 * functional store, because our purpose is not to explain mutation
 * but to explain gc.
 */

import scala.collection.mutable.ArraySeq

/* This is the well-known syntax of our language: FAE with boxes. */

sealed abstract class Exp
case class Num(n: Int) extends Exp
case class Id(name: Symbol) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp
case class If0(cond: Exp, thenExp: Exp, elseExp: Exp) extends Exp
implicit def num2exp(n: Int) = Num(n)
implicit def id2exp(s: Symbol) = Id(s)
case class Fun(param: Symbol, body: Exp) extends Exp
case class App (funExpr: Exp, argExpr: Exp) extends Exp
def wth(x: Symbol, xdef: Exp, body: Exp) : Exp = App(Fun(x,body),xdef)

case class NewBox(e: Exp) extends Exp
case class SetBox(b: Exp, e: Exp) extends Exp
case class OpenBox(b: Exp) extends Exp
case class Seq(e1: Exp, e2: Exp) extends Exp

/* We will equip our values with a mutable flag that is useful for
 * mark-and-sweep garbage collection. In real systems it is
 * implemented as a bit flag, or, if the so-called "tri-color
 * algorithm" is used, with two bit flags.
 */

abstract class Value { 
  var marked : Boolean = false
}

/* We will also use a mutable map instead of a map for environments.
 * This is not needed for mark-and-sweep, but for copying garbage
 * collectors such as Cheney's semi-space garbage collection
 * algorithm.
 */

type Env = scala.collection.mutable.Map[Symbol, Value]
case class NumV(n: Int) extends Value
case class ClosureV(f: Fun, env: Env) extends Value
case class AddressV(a: Int) extends Value

/* To be able to experiment with different store and gc designs, we
 * create an interface for stores. The stack parameter in malloc is
 * needed during gc to determine the root nodes from which the
 * algorithms can start.
 */

trait Store {
  def malloc(stack: List[Env], v: Value) : Int
  def update(index: Int, v: Value) : Unit
  def apply(index: Int) : Value
}

/* In our interpreter, the stack of environments is only implicitly
 * available on the stack of the meta-language. To reify the call-
 * stack we need to make it explicit. We do so by constructing the
 * stack explicitly and passing it as parameter. The first element
 * of the stack is the current environment; the rest is only needed
 * for gc.
 */

def eval(e: Exp, stack: List[Env], store: Store) : Value = e match {

  case Num(n) => NumV(n)

  case Id(x) => stack.head(x)

  case f@Fun(_, _) => ClosureV(f, stack.head)

  /* With a mutable store, we do not have to thread it according to
   * the order of evaluation any more.
   */

  case If0(cond, thenExp, elseExp)
    => eval(cond, stack, store) match {
         case NumV(0) => eval(thenExp, stack, store)
         case _       => eval(elseExp, stack, store)
       }

  /* The mutable store allows us to take advantage of Scala's
   * evaluation order and perform two pattern matchings
   * simultaneously.
   */

  case Add(l, r)
    => (eval(l, stack, store), eval(r, stack, store)) match {
         case (NumV(v1), NumV(v2)) => NumV(v1 + v2)
         case _ => sys.error("can only add numbers")
       }

  case Mul(l, r)
    => (eval(l, stack, store), eval(r, stack, store)) match {
         case (NumV(v1), NumV(v2)) => NumV(v1 * v2)
         case _ => sys.error("can only multiply numbers")
       }

  /* A new environment should be pushed onto the stack only when
   * binding occurs. Where exactly in BCFAE do bindings happen?
   */

  case App(f, a)
    => eval(f, stack, store) match {
         case ClosureV(f, cEnv)
           => eval(
                f.body,
                (cEnv + (f.param -> eval(a, stack, store))) :: stack,
                store
              )
         case _ => sys.error("can only apply functions")
       }

  /* The mutable store allows us to implement Seq-expression
   * in terms of sequencing in Scala itself.
   */

  case Seq(e1, e2)
    => eval(e1, stack, store); eval(e2, stack, store)

  case NewBox(e: Exp)
    => {
         val a = store.malloc(stack, eval(e, stack, store))
         AddressV(a)
       }

  case SetBox(b: Exp, e: Exp)
    => eval(b, stack, store) match {
         case AddressV(a)
           => {
                val ev = eval(e, stack, store)
                store.update(a, ev)
                ev
              }
         case _ => sys.error("can only set boxes")
       }

  case OpenBox(b: Exp)
    => eval(b, stack, store) match {
         case AddressV(a) => store(a)
         case _ => sys.error("can only open boxes")
       }
}
