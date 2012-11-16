/*
Programming languages and types

Exercise session E on 19.11.2012

Hand in
   - anytime
   - as a single .scala file
   - by E-Mail to pllecture@informatik

Solution will be posted before 26.11.12, 1000 hrs.

The tutor shall give feedback to each submission, without giving
points. Homework does not count toward course requirement. Do them for
your own benefit.

While everyone should write their own solution, it is recommended to
work face-to-face in small groups.


Garbage Collection
==================

You have the opportunity to make architectural changes to the garbage
collector of lecturenotes/10-gc.scala.

*/

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

// Let us remove the `marked` field of the class `Value`.
// If we think about the flag for garbage collection more carefully,
// then it becomes apparent that the flag should be a property of
// the memory cells instead of values.

abstract class Value /* {var marked : Boolean} */

// The classes `MemoryCell` and `Memory` implement this idea.
// Note that the flag of a memory cell is now an integer.
// It can hold more than 1 bit of information should your
// garbage collector require it.
//
// Note that the fields `flag` and `content` are mutable,
// enabling expressions such as
//
//    memory(5).flag = Marked
//
// Be sure to modify the default value of `flag` and `content`
// if you want it to be something other than `0` and `null`.

case class MemoryCell(var flag: Int = 0, var content: Value = null)

class Memory(length: Int) extends
scala.collection.mutable.ArraySeq[MemoryCell] (length) {
  // Primary constructor `new Memory(...)` executes statements
  // inside the class body.
  //
  // We want every position of the memory to be a memory cell.
  def resetMemory() : Unit = {
    this.indices.foreach(index => this.update(index, MemoryCell()))
  }

  resetMemory()
}

// Instead of the conceptual environment, we make the stack of
// variable bindings explicit.
//
// Note that the fields of `StackFrame` are mutable. You will
// need it if you choose to implement a copying garbage collector,
// or want to rename variables in the environment for some
// unfathomable reason.

case class StackFrame(var key: Symbol, var value: Value)

type Stack = List[StackFrame]

// Task a)
// -------
// Write a pair of functions to add bindings to the stack and
// lookup the value currently bound to an identifier. Be sure
// not to violate static scoping.


def addBinding(stack: Stack, x: Symbol, v: Value) : Stack =
  sys.error("Implement me!")

def lookupBinding(stack: Stack, x: Symbol) : Value =
  sys.error("Implement me!")


// The closure type saves the stack, which should contain all
// information about the bindings at the point of function
// definition.

case class ClosureV(f: Fun, stack: Stack) extends Value

case class NumV(n: Int) extends Value
case class AddressV(a: Int) extends Value

// The store interface is unmodified.

trait Store {
  def malloc(stack: Stack, v: Value) : Int
  def update(index: Int, v: Value) : Unit
  def apply(index: Int) : Value
}

// We retain the store without garbage collection so that
// you can test the `eval` function below. Changes are made
// to use the new memory abstraction.

class NoGCStore(size: Int) extends Store {
  val memory = new Memory(size)
  var nextFreeAddr : Int = 0
  def malloc(stack: Stack, v: Value) : Int = {
    val x = nextFreeAddr
    if (x >= size) sys.error("out of memory")
    nextFreeAddr += 1
    update(x, v)
    x
  }
  def update(index: Int, v: Value) : Unit = memory(index).content = v
  def apply(index: Int) = memory(index).content
}

// Task b)
// -------
// Rewrite the `eval` function, incorporating the stack of bindings.
// Task a) may help.
//
// You may assume that the store is mutable.

def eval(e: Exp, stack: Stack, store: Store) : Value = e match {

  case Num(n) => sys.error("Implement me!")

  case Id(x) => sys.error("Implement me!")

  case f@Fun(_, _) => sys.error("Implement me!")

  case If0(cond, thenExp, elseExp) => sys.error("Implement me!")

  case Add(l, r) => sys.error("Implement me!")

  case Mul(l, r) => sys.error("Implement me!")

  case App(f, a) => sys.error("Implement me!")

  case Seq(e1, e2) => sys.error("Implement me!")

  case NewBox(e: Exp) => sys.error("Implement me!")

  case SetBox(b: Exp, e: Exp) => sys.error("Implement me!")

  case OpenBox(b: Exp) => sys.error("Implement me!")
}

// Task c)
// -------
// Please design your own garbage collector.
// Feel free to modify everything.

class MyAwesomeStore(size: Int) extends Store {

  val memory = new Memory(size)

  // Put value in a newly allocated memory cell and return the address
  def malloc(stack: Stack, v: Value) : Int = {
    sys.error("Implement me!")
  }

  // The `update` and `apply` methods are identical to
  // those of `NoGCStore`. Feel free to modify them
  // if you feel something useful toward garbage collection
  // could be done here.

  def update(index: Int, v: Value) : Unit = memory(index).content = v

  def apply(index: Int) = memory(index).content
}
