// This is the Reader monad, abstracting the passing of
// environments.
//
// In most cases of this example, `R` is the environment type
// `Map[Symbol, Int]`, `A` is the value type `Int`, and `runReader` 
// computes a value from an initial environment.

case class Reader[R, A](runReader : R => A) {

  def turn(a: A) = Reader[R, A](_ => a)
  // Equivalent to `return` in Haskell.
  // If we call this method on an object called `re`,
  // we can write
  //
  //     re.turn(n)
  //
  // or equivalently,
  //
  //     re turn n
  //

  // Equivalent to `>>=` in Haskell.
  def >>=[B](f: A => Reader[R, B]) = Reader[R, B](
    (r: R) => f(this.runReader(r)).runReader(r)
  )
}

// Useful for getting the current environment.
def askR[A] = Reader[A, A](identity)

// Useful for changing the environment in a subcomputation.
def localR[R, S, A](f: R => S, m: Reader[S, A]) : Reader[R, A] =
  Reader[R,A](r => m.runReader( f(r) ) )

// Environment-based WAE interpreter using the Reader monad
sealed abstract class Exp 
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

def eval(e: Exp) : Reader[Env, Int] = {
  val re = Reader[Env, Int](_ => sys error "Return-only Reader")
  e match {
    case Num(n) => re turn n
    case Add(lhs, rhs) => eval(lhs) >>= ((v1) =>
      eval(rhs) >>= ((v2) =>
        re turn (v1 + v2)
    ))
    case Mul(lhs, rhs) => eval(lhs) >>= ((v1) =>
      eval(rhs) >>= ((v2) =>
        re turn (v1 * v2)
    ))
    case Id(x) => askR[Env] >>= (env =>
      re turn env(x)
    )
    case With(x, xdef, body) => eval(xdef) >>= (xv =>
      localR[Env, Env, Int](
        env => env + (x -> xv),
        eval(body)
      )
    )
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

