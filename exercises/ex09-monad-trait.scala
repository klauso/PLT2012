// Monad trait
// Written by Cai Yufei
// According to ideas of Jonathan Brachthaeuser

trait Monad[A] {

  // The Type
  // ========
  //
  // A variant of the following line must be repeated in every class 
  // implementing the Monad interface. It gives a name `M` to each
  // class implementing the Monad trait. The name is useful in various
  // places, not the least in ensuring that the particular monad does
  // not change during a bind operation, even though the content may.

  type M[A] <: Monad[A]

  // If MyMonad[A] extends Monad[A], it should declare instead:
  //
  // type M[A] = MyMonad[A]


  // Return
  // ======
  //
  // We force subclasses to implement a `return` method
  // inside a singleton object.

  def mReturn[B](a: B) : M[B]

  // The problem is, an instance of a particular monad class
  // is needed to invoke `mReturn`. For better user-friendliness,
  // subclasses should implement `mReturn` via a constructor,
  // which can be invoked outside the class definition without
  // any "template" instance:
  //
  // def mReturn[B](a: B) : M[B] = new MyMonad(a)
  // def this(a: A) = this( /* implementation of `return` */ )


  // Bind
  // ====
  //
  // Let us rename `bind` to `flatMap` in order to take advantage of
  // Scala's do-notation, called "for-comprehension".

  def mBind[B](f: A => M[B]) : M[B]


  // Unimportant
  // ===========
  //
  // `map` and `flatmap` are here to make Scala's do-notation, called
  // "for-comprehension", work. Subclasses should ignore it.

  final def flatMap[B](f: A => M[B]) : M[B] = mBind(f)
  final def map[B](f: A => B) : M[B] = flatMap(x => mReturn( f(x) ))

}


// This is the Reader monad, abstracting the passing of
// environments.
//
// In most cases of this example, `R` is the environment type
// `Map[Symbol, Int]`, `A` is the value type `Int`, and `runReader` 
// computes a value from an initial environment.

case class Reader[R, A](runReader: R => A) extends Monad[A] {

  type M[A] = Reader[R, A]

  def this(a: A) = this(_ => a)
  def mReturn[B](a: B) : M[B] = new Reader(a)

  def mBind[B](f: A => Reader[R, B]) = Reader[R, B](
    r => f(this runReader r) runReader r
  )

}


// Useful for getting the current environment.

def askR[A] = Reader[A, A](identity)


// Useful for changing the environment in a subcomputation,
// but extremely awkward when used together with
// for-comprehension. We don't make use if it any more.
//
// def localR[R, S, A](f: R => S, m: Reader[S, A]) : Reader[R, A] =
//  Reader[R,A](r => m runReader f(r))

// Environment-based WAE interpreter using the Reader monad

abstract class Exp 
case class Num(n: Int) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp
case class Id(x: Symbol) extends Exp 
case class With(x: Symbol, xdef: Exp, body: Exp) extends Exp
implicit def num2exp(n: Int) = Num(n)
implicit def sym2exp(x: Symbol) = Id(x)

type Env = Map[Symbol, Int]

// What `eval` computes is an instance of the monad Reader[Env, Int].
// It has one field, `runReader`, whose meaning should be clear from
// its type `Env => Int`.

def eval(e: Exp) : Reader[Env, Int] = e match {

  case Num(n) => new Reader(n)

  case Add(lhs, rhs) => for {
    v1 <- eval(lhs)
    v2 <- eval(rhs)
  } yield (v1 + v2)

  case Mul(lhs, rhs) => for {
    v1 <- eval(lhs)
    v2 <- eval(rhs)
  } yield (v1 * v2)

  case Id(x) => for {
    env <- askR
  } yield env(x)

  case With(x, xdef, body) => for {
    env <- askR
    xv  <- eval(xdef)
  } yield eval(body) runReader (env + (x -> xv))

}

// Tests from notes on WAE.
val test1 = With('x, 5, Add('x,'x))
val test2 = With('x, 5, Add('x, With('x, 3,10)))
val test3 = With('x, 5, Add('x, With('x, 3,'x)))
val test4 = With('x, 5, Add('x, With('y, 3,'x)))

def runTest(test: Exp) = eval(test) runReader Map()

assert(runTest(test1) == 10)
assert(runTest(test2) == 15)
assert(runTest(test3) ==  8) 
assert(runTest(test4) == 10)


// A second example: transliteration of Haskell's Maybe monad

object Maybe{

  sealed abstract class Maybe[A] extends Monad[A] {
    type M[A] = Maybe[A]

    def mReturn[B](a: B) : M[B] = Just(a)

    def mBind[B](f: A => M[B]) : M[B] = this match {
      case Nothing() => Nothing()
      case Just(a)   => f(a)
    }
  }

  case class Just[A](a: A) extends Maybe[A]
  case class Nothing[A]() extends Maybe[A]

}
