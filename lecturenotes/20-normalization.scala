/* Programming Languages and Types, Winter term 2012/13
 *
 * Substitute lecture by Tillmann Rendel, Winter term 2012/13
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

object Example {
  import Syntax._

  val term = App(Fun('y, Fun('x, Add('x, Add('y, 1)))), 2)
}

object Semantics {
  type Domain = Env => Value

  type Env = Map[Symbol, Value]

  abstract sealed class Value
  case class Num(n : Int) extends Value
  case class Id(name : Symbol) extends Value
  case class Add(lhs : Value, rhs : Value) extends Value
  case class Fun(f : Value => Value) extends Value
  case class App(fun : Value, arg : Value) extends Value

  def possiblyFunctional(v : Value) : Boolean = v match {
    case Fun(_) => true
    case App(_, _) => true
    case Id(_) => true
    case _ => false
  }

  def possiblyNumeric(v : Value) : Boolean = v match {
    case Num(_) => true
    case Add(_, _) => true
    case App(_, _) => true
    case Id(_) => true
    case _ => false
  }

  def num(n : Int) : Domain =
    (env : Env) => Num(n)

  def id(x : Symbol) : Domain =
    (env : Env) => env(x)

  def add(lhs : Domain, rhs : Domain) : Domain = 
    (env : Env) => (lhs(env), rhs(env)) match {
      case (Num(n1), Num(n2)) => Num(n1 + n2)
      case (lVal, rVal) if (possiblyNumeric(lVal) && possiblyNumeric(rVal)) => Add(lVal, rVal)
      case _ => sys.error("can only add numbers")
    }

  def fun(x : Symbol, body : Domain) =
    (env : Env) => Fun(arg => body(env + (x -> arg)))

  def app(fun : Domain, arg : Domain) : Domain =
    (env : Env) => fun(env) match {
      case Fun(f) => f(arg(env))
      case fVal if possiblyFunctional(fVal) => App(fVal, arg(env))
      case _ => sys.error("can only apply functions")
    }
}

object Evaluation {
  def eval(e : Syntax.Exp) : Semantics.Domain = e match {
    case Syntax.Num(n) => Semantics.num(n)
    case Syntax.Id(x) => Semantics.id(x)
    case Syntax.Add(e1, e2) => Semantics.add(eval(e1), eval(e2))
    case Syntax.Fun(x, e) => Semantics.fun(x, eval(e))
    case Syntax.App(e1, e2) => Semantics.app(eval(e1), eval(e2))
  }
}

object Reification {
  var i = 0

  def fresh() : Symbol = {
    i += 1
    Symbol("x" + i)
  }

  def reify(v : Semantics.Value) : Syntax.Exp = v match {
    case Semantics.Id(name) => Syntax.Id(name)
    case Semantics.Num(n) => Syntax.Num(n)
    case Semantics.Add(lhs, rhs) => Syntax.Add(reify(lhs), reify(rhs))
    case Semantics.Fun(f) => {
      val x = fresh()
      Syntax.Fun(x, reify(f(Semantics.Id(x))))
    }
    case Semantics.App(fun, arg) => Syntax.App(reify(fun), reify(arg))
  }
}


object Test {
  import Reification.reify
  import Evaluation.eval

  def norm(e : Syntax.Exp) : Syntax.Exp = 
    Reification.reify(eval(e)(Map()))

  val test = norm(Example.term)
}
