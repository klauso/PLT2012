/* Programming Languages and Types, Winter term 2012/13
 *
 * Lecture on the structure of syntax and semantics;
 * and their connection by evaluation (in one direction)
 * and reification (in the other direction).
 * 
 * Substitute lecture by Tillmann Rendel
 */

  
/* INTRODUCTION
 * ============
 *
 * The motivating example for this lecture is the following
 * FAE program:
 *
 *     App(Fun('y, Fun('x, Add('x, Add('y, 1)))), 2)
 *
 * Evaluating this program yields ...
 *
 * ... in the substitution-based interpreter:
 *
 *     Fun('x, Add('x, Add(2, 1)))
 *
 * ... in the environment-based interpreter:
 *
 *     FunV('x, Add('x, Add('y, 1)), 'y -> 2)
 *
 * Neither of these interpreters computes 2 + 1 = 3.
 * This computation is left for later, when the function
 * is actually called.
 *
 * There are (at least) two reasons for performing
 * some computations in a function body earlier:
 *
 *  (1) It can save work: If the function is called
 *      often, we should do as much work as possible
 *      before constructing the function value.
 *
 *  (2) It can help us to recognize equivalent programs.
 *
 * To understand the second point, we have to understand
 * that there are many programs that describe the same
 * function. For example:
 *
 *     Abs('x, Add('x, Add(1, 1)))
 *     Abs('x, Add(1, Add('x, 1)))
 *     Abs('x, Add('x, 2))
 *
 * All of these programs describe the function that adds
 * two to its argument. We say that these programs are
 * equivalent. Among this set of equivalent programs, the
 * last program is in a normal form, because it does not
 * contain any subcomputations that we could perform right
 * now. One goal of today's lecture is to transform a program
 * into its normal form.
 *
 * I also want to use this lecture to introduce my idea of how
 * an interpreter should be structured: I believe that one
 * should carefully distinguish between the *syntactical* and
 * the *semantical* structure of a language.
 *
 *             Syntax                           Semantics    
 * -------------------------------------------------------------
 * Objects:    Terms / Expressions / Programs   Values
 * Structure:  substitution, ...                application, ...
 * -------------------------------------------------------------
 *
 * Evaluation is a mapping from Syntax to Semantics:
 *
 *     Syntax    ---evaluation-->  Semantics
 *
 * SYNTAX
 * ======
 *
 * We start with the syntax of FAE as presented in earlier
 * lectures. I put everything into a Syntax object to distinguish
 * syntax and semantics more clearly from each other.
 */

object Syntax {
  sealed abstract class Exp
  case class Num(n: Int) extends Exp
  case class Id(name: Symbol) extends Exp
  case class Add(lhs: Exp, rhs: Exp) extends Exp
  case class Fun(param: Symbol, body: Exp) extends Exp
  case class App (funExpr: Exp, argExpr: Exp) extends Exp

  implicit def num2exp(n: Int) = Num(n)
  implicit def id2exp(s: Symbol) = Id(s)
  def wth(x: Symbol, xdef: Exp, body: Exp) : Exp = App(Fun(x, body), xdef)
}

/* Examples
 * ========
 *
 * As example terms, we use the motivating example from above, with
 * two different ways to apply the function to 2. Either directly,
 * or indirectly via an application function written in FAE.
 */

object Example {
  import Syntax._

  val TERM = Fun('y, Fun('x, Add('x, Add('y, 1))))
  val APPLY = Fun('f, Fun('x, App('f, 'x)))

  val TEST1 = App(TERM, 2)
  val TEST2 = App(App(APPLY, TERM), 2)
}

/* SEMANTICS
 * =========
 *
 * We now define the semantic structure of FAE.
 * In this first version of the semantics, we only include
 * features that we need for evaluation.
 *
 * Notes:
 *
 *  (1) The semantics is *only* about values, and not about
 *      expressions at all. We make this explicit by not even
 *      importing the members of the Syntax object above.
 * 
 *  (2) The interpreter is meta-circular: FAE numbers are
 *      represented as Scala integers, and FAE functions
 *      are represented as Scala functions.
 *
 *  (3) We introduce a name for the function type Env => Value.
 *      This will be the return type of the eval function. One
 *      way to understand the name "domain" is: From all the
 *      things in the (mathematical) world, we select a subset
 *      of things we want to talk about in our language FAE, and
 *      this subset of things of interest forms the domain of our
 *      language.
 *      (Not to be confused with the domain of a function, which
 *      is the subset of all the things in the world a function
 *      can be applied to).
 *
 *  (4) We have a function for each syntactic construct of FAE.
 *      These functions operate on things in the Domain. They
 *      perform all the work that is necessary to implement the
 *      syntactic construct.
 */

object Semantics {
  type Domain = Env => Value

  type Env = Map[Symbol, Value]

  abstract sealed class Value
  case class Fun(f : Value => Value) extends Value
  case class Num(n : Int) extends Value

  def num(n : Int) : Domain =
    (env : Env) => Num(n)

  def id(x : Symbol) : Domain =
    (env : Env) => env(x)

  def add(lhs : Domain, rhs : Domain) : Domain =
    (env : Env) => (lhs(env), rhs(env)) match {
      case (Num(n1), Num(n2)) => Num(n1 + n2)
      case _ => sys.error("not happy")
    }

  def app(fun : Domain, arg : Domain) : Domain =
    (env : Env) => fun(env) match {
      case Fun(f) => f(arg(env))
      case _ => sys.error("not happy")
    }
 
  def fun(x : Symbol, body : Domain) : Domain =
    (env : Env) => Fun(arg => body(env + (x -> arg)))
}

/* EVALUATION
 * ==========
 *
 * Evaluation maps syntactic structure to semantic structure.
 * All the hard work is done in the semantics above, so evaluation
 * is almost boring.
 */

object Evaluation {
  def eval(e : Syntax.Exp) : Semantics.Domain =
    e match {
      case Syntax.Num(n) => Semantics.num(n)
      case Syntax.Id(x) => Semantics.id(x)
      case Syntax.Add(e1, e2) => Semantics.add(eval(e1), eval(e2))
      case Syntax.Fun(x, e) => Semantics.fun(x, eval(e))
      case Syntax.App(e1, e2) => Semantics.app(eval(e1), eval(e2))
    }
}

/* REIFICATION
 * ===========
 *
 * Reification is the inverse of evaluation:
 * 
 *            ---evaluation-->
 *     Syntax                   Semantics
 *            <--reification--
 *
 * Reification comes from latin "res" = thing. It means to
 * represent something abstract as something more concrete.
 * In our case, the abstract is a value in the domain,
 * and the concrete is an FAE expression.
 *
 * The first step is to extend the semantic structure with
 * support for *symbolic computation*. All changed parts are
 * marked with comments.
 */

object Semantics2 {
  type Domain = Env => Value

  type Env = Map[Symbol, Value]

  abstract class Value
  case class Fun(f : Value => Value) extends Value
  case class Num(n : Int) extends Value

  // Three new case classes for symbolic values:
  case class Id(x : Symbol) extends Value
  case class Add(lhs : Value, rhs : Value) extends Value
  case class App(fun : Value, arg : Value) extends Value

  // A new helper function to decide whether a value
  // could mean a number
  def canBeNumber(v : Value) : Boolean = v match {
    case Fun(_) => false
    case Num(_) => true
    case Id(_) => true
    case Add(_, _) => true
    case App(_, _) => true
  }

  // A new helper function to decide whether a value
  // could mean a function
  def canBeFunction(v : Value) : Boolean = v match {
    case Fun(_) => true
    case Num(_) => false
    case Id(_) => true
    case Add(_, _) => false
    case App(_, _) => true
  }

  def num(n : Int) : Domain =
    (env : Env) => Num(n)

  def id(x : Symbol) : Domain =
    (env : Env) => env(x)

  def add(lhs : Domain, rhs : Domain) : Domain =
    (env : Env) => (lhs(env), rhs(env)) match {
      case (Num(n1), Num(n2)) => Num(n1 + n2)
      // new case for symbolic addition:
      case (val1, val2) if canBeNumber(val1) && canBeNumber(val2) => Add(val1, val2)
      case _ => sys.error("not happy")
    }

  def app(fun : Domain, arg : Domain) : Domain =
    (env : Env) => fun(env) match {
      case Fun(f) => f(arg(env))
      // new case for symbolic application:
      case (funVal) if canBeFunction(funVal) => App(funVal, arg(env))
      case _ => sys.error("not happy")
    }
 
  def fun(x : Symbol, body : Domain) : Domain =
    (env : Env) => Fun(arg => body(env + (x -> arg)))
}

/* This enhanced semantic structure is still suitable for
 * evaluation. We don't have to change anything at all in
 * the evaluation function:
 */

object Evaluation2 {
  def eval(e : Syntax.Exp) : Semantics2.Domain =
    e match {
      case Syntax.Num(n) => Semantics2.num(n)
      case Syntax.Id(x) => Semantics2.id(x)
      case Syntax.Add(e1, e2) => Semantics2.add(eval(e1), eval(e2))
      case Syntax.Fun(x, e) => Semantics2.fun(x, eval(e))
      case Syntax.App(e1, e2) => Semantics2.app(eval(e1), eval(e2))
    }
}

/* And the enhanced semantics structure with its support
 * for symbolic computation is also suitable for reification.
 *
 * Notes:
 *
 *  (1) We use a cheap trick for generating fresh identifiers.
 *      Don't do that at home.
 *
 *  (2) The first four cases of reify are straight-forward.
 *
 *  (3) The case for functions is all-important.
 */

object Reification {
  var i = 0

  def fresh() : Symbol = {
    i += 1
    Symbol("x" + i)
  }

  def reify(v : Semantics2.Value) : Syntax.Exp = v match {
    case Semantics2.Id(name) => Syntax.Id(name)
    case Semantics2.Num(n) => Syntax.Num(n)
    case Semantics2.Add(lhs, rhs) => Syntax.Add(reify(lhs), reify(rhs))
    case Semantics2.App(fun, arg) => Syntax.App(reify(fun), reify(arg))

    case Semantics2.Fun(f) => {
      val x = fresh()
      Syntax.Fun(x, reify(f(Semantics2.Id(x))))
    }
  }
}

/* Going from syntax to semantics and back is normalization.
 */

def norm(e : Syntax.Exp) : Syntax.Exp =
  Reification.reify(Evaluation2.eval(e)(Map()))

/* Some tests.
 */

val test1 = norm(Example.TEST1)
val test2 = norm(Example.TEST2)

/* SUMMARY
 * =======
 *
 * We implemented an interpreter where syntax and semantics
 * is strictly separated. Most of the hard work is in the
 * semantics, in functions like app and add. Evaluation is
 * very simple: We just map the syntactic structure to the
 * semantic structure. We also defined reification, the
 * inverse of evaluation. This required two tricks: (1) We
 * enhanced the semantics with support for symbolic computation,
 * effectively adding a copy of all Exp constructors to the
 * Value type. (2) In the case for the reifications of
 * functions, we apply the function to a fresh identifier.
 */
