// Monad trait

// TODO
//
// mReturn and mBind doesn't know to look for implicit monad
// based on return type. May we copy CanBuildFrom[Repr, B, That]?

trait Monad[ M[_] ] {
  def mReturn[A](a: A) : M[A]
  def mBind[A, B](m: M[A], f: A => M[B]) : M[B]
}

implicit def mReturn[M[_], A](a: A)(implicit p: Monad[M])
: M[A] = p.mReturn(a)
implicit def mBind[M[_], A, B](m: M[A], f: A => M[B])(implicit p: Monad[M])
: M[B] = p.mBind(m, f)
implicit def comprehensionSyntax[M[_], A](m: M[A])(implicit p: Monad[M])
= new {
  def flatMap[B](f: A => M[B]) : M[B] = mBind(m, f)
  def map[B](f: A => B) : M[B] = flatMap(x => mReturn(f(x)))
}


// This is the Reader monad, abstracting the passing of
// environments.
//
// In most cases of this example, `R` is the environment type
// `Map[Symbol, Int]`, `A` is the value type `Int`, and `runReader` 
// computes a value from an initial environment.

case class Reader[R, A](runReader: R => A) {

  type M[A] = Reader[R, A]

  implicit object ReaderMonad extends Monad[M] {
    def mReturn[A](a: A) = Reader(_ => a)
    def mBind[A, B](m: Reader[R, A], f: A => Reader[R, B]) = Reader[R, B](
      r => f(m runReader r) runReader r
    )
  }

}

implicit def nastyHack[R, A] = new Reader[R,A](_ => sys error ">_<").ReaderMonad


// A second example: transliteration of Haskell's Maybe monad

sealed abstract class Maybe[A]

case class Just[A](a: A) extends Maybe[A]
case class Nothing[A]() extends Maybe[A]

implicit object MaybeMonad extends Monad[Maybe] {
  def mReturn[A](a: A) : Maybe[A] = Just(a)
  def mBind[A, B](m: Maybe[A], f: A => Maybe[B]) : Maybe[B] = m match {
    case Nothing() => Nothing()
    case Just(a) => f(a)
  }
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
//
// I hate EnvReader.

type EnvReader[A] = Reader[Env, A]

def eval(e: Exp)
(implicit monad: Monad[EnvReader])
: EnvReader[Int] = {
  e match {

    // mReturn is good if
    case Num(n) => mReturn(n)

    case Add(lhs, rhs) => for {
      v1 <- eval(lhs)
      v2 <- eval(rhs)
    } yield (v1 + v2)

    case Mul(lhs, rhs) => for {
      v1 <- eval(lhs)
      v2 <- eval(rhs)
    } yield (v1 * v2)

    case Id(x) => for {
      env <- askR : EnvReader[Env]
    } yield env(x)

    case With(x, xdef, body) => for {
      env <- askR : EnvReader[Env]
      xv  <- eval(xdef)
    } yield eval(body) runReader (env + (x -> xv))
  }
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
