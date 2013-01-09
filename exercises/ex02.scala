/*
Programming languages and types

Exercise session B on 29.10.2012

Hand in
   - anytime
   - as a single .scala file
   - by E-Mail to pllecture@informatik

Solution will be posted before 05.11.12, 1000 hrs.

Please feel free to contribute to the discussion in German. Cai will
likely understand you if you speak slowly and clearly.

The tutor shall give feedback to each submission, without giving
points. Homework does not count toward course requirement. Do them for
your own benefit.

While everyone should write their own solution, it is recommended to
work face-to-face in small groups. As with lecture notes, this file
can be checked and experimented with by running the scala interpreter
and typing

scala> :l A.scala


Contents
========

1. Terminating recursive functions
2. Dynamic scoping
*/

sealed abstract class Exp 
case class Num(n: Int) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp
case class Id(x: Symbol) extends Exp 
case class With(x: Symbol, xdef: Exp, body: Exp) extends Exp
case class Call(f: Symbol, args: List[Exp]) extends Exp
implicit def num2exp(n: Int) = Num(n)
implicit def sym2exp(x: Symbol) = Id(x)
case class FunDef(args: List[Symbol], body: Exp) 
type Funs = Map[Symbol,FunDef]
type Env = Map[Symbol,Int]
def implement_me = Id('Implement_me)
def evaluate_me = 0

/*
1. Terminating recursive functions
==================================
*/

// Extend F1AE with the construct If0(cond, true_exp, false_exp)
// which evaluates to true_exp if cond is zero and to false_exp
// otherwise.

case class If0(cond : Exp, true_exp : Exp, false_exp : Exp) extends Exp

def eval(e : Exp, funs : Funs = Map(), env : Env = Map()) : Int = e match {
  case Num(n)              => n
  case Id(x)               => env(x)
  case Add(lhs,rhs)        => eval(lhs, funs, env) + eval(rhs, funs, env)
  case Mul(lhs,rhs)        => eval(lhs, funs, env) * eval(rhs, funs, env)
  case With(x, xdef, body) =>
         eval(body, funs, env + ((x, eval(xdef, funs, env))))
  case Call(f, args)       => {
         val fd = funs(f)
         if (fd.args.size != args.size)
           sys.error("Mismatch of parameter number on invocation of " + f)
         val vargs = args.map(eval(_, funs, env))
         val newenv = Map() ++ fd.args.zip(vargs)
         eval(fd.body, funs, newenv)
       }

// a) Implement the evaluation of If0

  case If0(cond, te, fe)   => evaluate_me
}

// b) Write a function `factorial` mapping n to
//    n! = n*(n - 1)*(n - 2)*(n - 3)* ... * 1

val factorial = 'factorial -> FunDef('n :: Nil,
  implement_me
)

// c) Write the function `fib` that computes the n-th fibonacci number:
//
//    fib(0) = 1
//    fib(1) = 1
//    fib(n) = fib(n - 1) + fib(n - 2)

val fib = 'fib -> FunDef('n :: Nil,
  implement_me
)

// d) Write the Ackermann function in the extended F1AE:
//
//    ack(m, n) = |   n + 1                       if   m = 0
//                |   ack(m - 1, 1)               if   m > 0 and n = 0
//                |   ack(m - 1, ack(m, n - 1))   if   m > 0 and n > 0

val ack = 'ack -> FunDef('m :: 'n :: Nil,
  implement_me
)

val funs = Map(factorial, fib, ack)


// Test cases. Uncomment to run.

// The factorials of 0,1,...,9 should be 1,1,...,362880.
/*
def call_factorial(n : Int) : Int = eval(Call('factorial, n :: Nil), funs)
assert(
List(0, 1, 2, 3,  4,   5,   6,    7,     8,      9).map(call_factorial) ==
List(1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880))
*/

// The 0th,1st,...,9th fibonacci numbers should be 1,1,...,55.
/*
def call_fib(n : Int) : Int = eval(Call('fib, n :: Nil), funs)
assert(
List(0, 1, 2, 3, 4, 5,  6,  7,  8,  9).map(call_fib) ==
List(1, 1, 2, 3, 5, 8, 13, 21, 34, 55))
*/

// ack(1, 0) ==  2 ; ack(1, 1) ==   3 ; ack(1, 2) ==   4 ; ...
// ack(3, 3) == 61 ; ack(3, 4) == 125 ; ack(3, 5) == 253
/*
def call_ack(m : Int, n : Int) = eval(Call('ack, List(m, n)), funs)
assert(((
List(1, 1, 1, 1, 1, 1, 2, 2, 2, 2,  2,  2, 3,  3,  3,  3,   3,   3),
List(0, 1, 2, 3, 4, 5, 0, 1, 2, 3,  4,  5, 0,  1,  2,  3,   4,   5)).
zipped.map(call_ack(_, _))) ==
List(2, 3, 4, 5, 6, 7, 3, 5, 7, 9, 11, 13, 5, 13, 29, 61, 125, 253))
*/

/*
2. Dynamic scoping
==================
*/

// We will implement a more radical version of dynamic scoping than
// what was in the lecture notes. The scoping rules are thus:
//
// 1. With-expressions in the main programme affects everything
//    that occurs after it. For example:
//
//      Add(With('x, 5, 'x), 'x)
//
//    should evaluate to 10.
//
// 2. Actual parameters of functions are evaluated before the function
//    body and may, by rule 1, alter the overall environment of the
//    programme.
//
// 3. Free variables in function bodies take values according to the
//    calling environment.
//
// 4. Bindings introduced by With-expressions inside function bodies
//    have their effect limited inside their own function body and
//    have no effect on the outside world.
//
//
// There are hints toward two possible implementations.
//
// a. Do away with the code below and implement the evaluation through
//    scala mutable maps:
//
//      type Env = scala.collection.mutable.Map[Symbol, Int]
//
//    Do remember to call env.clone() judiciously to prevent the local
//    bindings inside function bodies from affecting the outside
//    universe.
//
// b. Complete the code below.
//    We proceed in "continuation passing style",
//    where each call to `eval_dynamic_scope` is given a continuation-
//    function, which represents the computation after the evaluation
//    of this term.

// A continuation maps a partial result and an environment
// to the final result.

type Continuation = (Int, Env) => Int

def eval_dynamic_scope(
  e    : Exp,
  funs : Funs = Map(),
  env  : Env = Map(),
  ctn  : Continuation = (result, _) => result
) : Int = e match {
  // Numbers yield a result; we can call the continuation and do the
  // rest of the computation.
  case Num(n)
    => ctn(n, env)
  // So are identifiers.
  case Id(x)
    => ctn(env(x), env)
  // For the sum of two subexpressions,
  // we evaluate the left-hand-side first,
  // giving it as continuation a function that will
  // evaluate the right-hand-side under the environment
  // after evaluation of the left-hand-side, and do the
  // rest of the computation  thereafter.
  case Add(lhs, rhs)
    => eval_dynamic_scope(
         lhs, funs, env,
         (value_lhs, env_after_lhs) =>
         eval_dynamic_scope(
            rhs, funs, env_after_lhs,
            (value_rhs, env_after_rhs) =>
            ctn(value_lhs + value_rhs, env_after_rhs)))
  // Please complete the implementation of Mul-, With-, Call-
  // and If0-expressions. Call-expressions are the most difficult.
  case Mul(lhs, rhs)
    => evaluate_me
  case With(x, xdef, body)
    => evaluate_me
  case Call(f, args)
    => evaluate_me
  case If0(cond, true_exp, false_exp)
    => evaluate_me
}

// Some test cases. Uncomment to run.

val e1 = Mul(Add(3, 4), Mul(2, 3))
val e2 = Mul(With('z, 6, 7), 'z)
val e3 = Add(With('hidden_factor, 7, 0), Call('multiply, List(6)))
val e4 = Call('multiply, List(With('hidden_factor, 7, 6)))

val multiply = 'multiply -> FunDef('n :: Nil, Mul('n, 'hidden_factor))
val dynamic_funs : Funs = Map(multiply)

// assert(42 == eval_dynamic_scope(e1))
// assert(42 == eval_dynamic_scope(e2))
// assert(42 == eval_dynamic_scope(e3, dynamic_funs))
// assert(42 == eval_dynamic_scope(e4, dynamic_funs))
