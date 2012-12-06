/*
* This lecture note is loosely based on the paper //A Functional
* Correspondence between Evaluators and Abstract Machines// by Olivier Danvy
* et al.
*
* Author: Yi Dai
* Date: 2012-12-05
*/

/* $ From Evaluators to Abstract Machines $
 *
 * In the first part of this lecture, we will look at how to derive an
 * abstract machine, called Krivine's machine, for the call-by-name lambda
 * calculus, from a standard interpreter by a series of program
 * transformations, namely closure conversion, CPS-transformation, and
 * defunctionalization.
 */

/* $$ Higher-Order Function $$
 *
 * This interpreter features higher-order functions in two senses:
 *
 * # Object-level functions are implemented by meta-level functions.  Since
 * {{eval}} returns such a function as result, {{eval}} is higher-order.
 *
 * # The operand, whose evaluation must be delayed, to an object-level
 * function is implemented by a meta-level function that takes no argument.
 * Since object-level function application is implemented by meta-level
 * function application, the meta-level function is higher-order.
 */
object HOF {
  sealed abstract class Exp
  sealed abstract class EVa  // Expressible Values
  sealed abstract class DVa  // Denotable Values

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  case class Prc(fun : DVa => EVa) extends EVa

  case class Prm(fun : () => EVa) extends DVa

  type Env = List[DVa]

  def eval(exp : Exp, env : Env) : EVa = exp match {
    case Var(ind) => env(ind) match {
      case Prm(fun) => fun()
    }
    case Abs(bod) => Prc(prm => eval(bod, prm :: env))
    case App(opr, opd) => eval(opr, env) match {
      case Prc(fun) => fun(Prm(() => eval(opd, env)))
    }
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil)
}

/* $$ Closure Conversion $$
 *
 * Closure conversion converts the representation of object-level functions
 * from meta-level functions to meta-level data structures, namely closures.
 * Closure conversion is a special form of defunctionalization.  It is
 * normally done before transforming the interpreter into continuation-passing
 * style to ease the task.
 */
object HOF_CC {
  sealed abstract class Exp
  sealed abstract class EVa
  sealed abstract class DVa

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[DVa]

  case class Clo(bod : Exp, sen : Env) extends EVa

  case class Thk(opd : Exp, sen : Env) extends DVa

  def apCl(clo : EVa, thk : DVa) : EVa = clo match {
    case Clo(bod, sen) => eval(bod, thk :: sen)
  }

  def apTh(thk : DVa) : EVa = thk match {
    case Thk(opd, sen) => eval(opd, sen)
  }

  def eval(exp : Exp, env : Env) : EVa = exp match {
    case Var(ind) => apTh(env(ind))
    case Abs(bod) => Clo(bod, env)
    case App(opr, opd) => apCl(eval(opr, env), Thk(opd, env))
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil)
}

/* $$$ Inlining $$$
 *
 * Inlining {{apCl}} and {{apTh}} gives an interpreter in direct style.
 */
object HOF_CC_Il {
  sealed abstract class Exp
  sealed abstract class EVa
  sealed abstract class DVa

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[DVa]

  case class Clo(bod : Exp, sen : Env) extends EVa

  case class Thk(opd : Exp, sen : Env) extends DVa

  def eval(exp : Exp, env : Env) : EVa = exp match {
    case Var(ind) => env(ind) match {
      case Thk(opd, sen) => eval(opd, sen)
    }
    case Abs(bod) => Clo(bod, env)
    case App(opr, opd) => eval(opr, env) match {
      case Clo(bod, sen) => eval(bod, Thk(opd, env) :: sen)
    }
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil)
}

/* $$ Continuation-Passing-Style Transformation $$ */

object HOF_CC_CPS {
  sealed abstract class Exp
  sealed abstract class EVa
  sealed abstract class DVa

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[DVa]

  case class Clo(bod : Exp, sen : Env) extends EVa

  case class Thk(opd : Exp, sen : Env) extends DVa

  type Ctn = EVa => EVa

  def eval(exp : Exp, env : Env, ctn : Ctn) : EVa = exp match {
    case Var(ind) => env(ind) match {
      case Thk(opd, sen) => eval(opd, sen, ctn)
    }
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      eval( opr, env
          , clo => clo match {
              case Clo(bod, sen) => eval(bod, Thk(opd, env) :: sen, ctn)
            } )
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil, eva => eva)
}

/* $$ Defunctionalization $$ */

object HOF_CC_CPS_DF {
  sealed abstract class Exp
  sealed abstract class EVa
  sealed abstract class DVa
  sealed abstract class Ctn

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[DVa]

  case class Clo(bod : Exp, sen : Env) extends EVa

  case class Thk(opd : Exp, env : Env) extends DVa

  case class IdC() extends Ctn
  case class ApC(opd : Exp, env : Env, ctn : Ctn) extends Ctn

  def apCt(ctn : Ctn, eva : EVa) : EVa = ctn match {
    case IdC() => eva
    case ApC(opd, env, ctn) => eva match {
      case Clo(bod, sen) => eval(bod, Thk(opd, env) :: sen, ctn)
    }
  }

  def eval(exp : Exp, env : Env, ctn : Ctn) : EVa = exp match {
    case Var(ind) => env(ind) match {
      case Thk(opd, sen) => eval(opd, sen, ctn)
    }
    case Abs(bod) => apCt(ctn, Clo(bod, env))
    case App(opr, opd) => eval(opr, env, ApC(opd, env, ctn))
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil, IdC())
}

/* $$$ Refactoring $$$
 *
 * Unifying the data structure for closure and thunk and listifying the data
 * structure for continuation gives an implementation of Krivine's machine.
 */
object KAM {
  sealed abstract class Exp
  sealed abstract class Clo

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Clo]

  case class Thk(exp : Exp, sen : Env) extends Clo

  type Ctn = List[Clo]

  def eval(exp : Exp, env : Env, ctn : Ctn) : Exp = exp match {
    case Var(ind) => env(ind) match {
      case Thk(opd, env) => eval(opd, env, ctn)
    }
    case Abs(bod) => ctn match {
      case Nil => Abs(bod)
      case (Thk(opd, sen) :: ctn) => eval(bod, Thk(opd, sen) :: env, ctn)
    }
    case App(opr, opd) => eval(opr, env, Thk(opd, env) :: ctn)
  }

  def intp(exp : Exp) : Exp = eval(exp, Nil, Nil) 
}

/* $$ Krivine's Abstract Machine $$ */

/* $ From Abstract Machines to Evaluators $ */

/* $$ The CEK Machine $$ */

object CEK {
  sealed abstract class Exp
  sealed abstract class EVa
  sealed abstract class Ctx

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[EVa]

  case class Clo(bod : Exp, sen : Env) extends EVa

  case class IdC() extends Ctx
  case class LAC(opd : Exp, env : Env, ctx : Ctx) extends Ctx
  case class RAC(clo : EVa, ctx : Ctx) extends Ctx

  def apCt(ctx : Ctx, eva : EVa) : EVa = ctx match {
    case IdC() => eva
    case LAC(opd, env, ctx) => eva match {
      case clo@Clo(_, _) => eval(opd, env, RAC(clo, ctx))
    }
    case RAC(Clo(bod, sen), ctx) => eval(bod, eva :: sen, ctx)
  }

  def eval(exp : Exp, env : Env, ctx : Ctx) : EVa = exp match {
    case Var(ind) => apCt(ctx, env(ind))
    case Abs(bod) => apCt(ctx, Clo(bod, env))
    case App(opr, opd) => eval(opr, env, LAC(opd, env, ctx))
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil, IdC())
}

/* $$ Refunctionalization $$ */

object CEK_RF {
  sealed abstract class Exp
  sealed abstract class EVa

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[EVa]

  case class Clo(bod : Exp, sen : Env) extends EVa

  type Ctx = EVa => EVa

  def eval(exp : Exp, env : Env, ctx : Ctx) : EVa = exp match {
    case Var(ind) => ctx(env(ind))
    case Abs(bod) => ctx(Clo(bod, env))
    case App(opr, opd) =>
      eval( opr, env
          , clo => eval( opd, env
                       , arg => clo match {
                           case Clo(bod, sen) => eval(bod, arg :: sen, ctx)
                         } ) )
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil, eva => eva) 
}

/* $$ Direct-Style Transformation $$ */

object CEK_RF_DS {
  sealed abstract class Exp
  sealed abstract class EVa

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[EVa]

  case class Clo(bod : Exp, sen : Env) extends EVa

  def eval(exp : Exp, env : Env) : EVa = exp match {
    case Var(ind) => env(ind)
    case Abs(bod) => Clo(bod, env)
    case App(opr, opd) => eval(opr, env) match {
      case Clo(bod, sen) => eval(bod, eval(opd, env) :: sen)
    }
  }

  def intp(exp : Exp, env : Env) : EVa = eval(exp, Nil)
}

/* $$ Higher-Order-Function Conversion $$ */

object CEK_RF_DS_HOF {
  sealed abstract class Exp
  sealed abstract class EVa

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[EVa]

  case class Prc(fun : EVa => EVa) extends EVa

  def eval(exp : Exp, env : Env) : EVa = exp match {
    case Var(ind) => env(ind)
    case Abs(bod) => Prc(arg => eval(bod, arg :: env))
    case App(opr, opd) => eval(opr, env) match {
      case Prc(fun) => fun(eval(opd, env))
    }
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil)
}




/****************
 * Rationalized *
 ****************

object HOF {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp
  case class Prc(fun : Imp => Imp) extends Imp

  type Env = List[Imp]

  def norm(imp : Imp, env : Env) : Imp = imp match {
    case Var(ind) => env(ind)
    case Abs(bod) => Prc(arg => norm(bod, arg :: env))
    case App(opr, opd) => norm(opr, env) match {
      case Prc(fun) => fun(norm(opd, env))
      case any => sys.error("Not a function designator: " + any)
    }
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil)
}

object HOF_CbNCPS {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  type Ctn = Imp => Imp

  case class Prc(fun : Imp => Ctn => Imp) extends Imp
  case class Cmp(fun : Ctn => Imp) extends Imp

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => env(ind) match {
      case Cmp(fun) => fun(ctn)
      case any => sys.error("Not a computation designator: " + any)
    }
    case Abs(bod) => ctn(Prc(cmp => ctn => norm(bod, cmp :: env, ctn)))
    case App(opr, opd) =>
      norm( opr, env
          , prc => prc match {
              case Prc(fun) => fun(Cmp(ctn => norm(opd, env, ctn)))(ctn)
              case any => sys.error("Not a function designator: " + any)
            } )
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

object HOF_CbNCPS_CC {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  case class Clo(bod : Imp, sen : Env) extends Imp
  case class Thk(opd : Imp, sen : Env) extends Imp

  type Ctn = Imp => Imp

  def apCl(clo : Imp, cmp : Imp, ctn : Ctn) : Imp = clo match {
    case Clo(bod, sen) => norm(bod, cmp :: sen, ctn)
    case any => sys.error("Not a function designator: " + any)
  }

  def apTh(thk : Imp, ctn : Ctn) : Imp = thk match {
    case Thk(opd, sen) => norm(opd, sen, ctn)
    case any => sys.error("Not a computation designator: " + any)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => apTh(env(ind), ctn)
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      norm( opr, env
          , clo => apCl(clo, Thk(opd, env), ctn) )
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

object HOF_CbNCPS_CC_DF {
  sealed abstract class Imp
  sealed abstract class Ctn

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  case class Clo(bod : Imp, sen : Env) extends Imp
  case class Thk(opd : Imp, sen : Env) extends Imp

  case class IdC() extends Ctn
  case class ApC(opd : Imp, sen : Env, ctn : Ctn) extends Ctn

  def apCl(clo : Imp, cmp : Imp, ctn : Ctn) : Imp = clo match {
    case Clo(bod, sen) => norm(bod, cmp :: sen, ctn)
    case any => sys.error("Not a function designator: " + any)
  }

  def apTh(thk : Imp, ctn : Ctn) : Imp = thk match {
    case Thk(opd, sen) => norm(opd, sen, ctn)
    case any => sys.error("Not a computation designator: " + any)
  }

  def apCt(ctn : Ctn, clo : Imp) : Imp = ctn match {
    case IdC() => clo
    case ApC(opd, sen, ctn) => apCl(clo, Thk(opd, sen), ctn)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => apTh(env(ind), ctn)
    case Abs(bod) => apCt(ctn, Clo(bod, env))
    case App(opr, opd) => norm(opr, env, ApC(opd, env, ctn))
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, IdC())
}

object HOF_CbVCPS {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  type Ctn = Imp => Imp

  case class Prc(fun : Imp => Ctn => Imp) extends Imp

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => ctn(env(ind))
    case Abs(bod) => ctn(Prc(arg => ctn => norm(bod, arg :: env, ctn)))
    case App(opr, opd) =>
      norm( opr, env
          , prc => norm( opd, env
                       , arg => prc match {
                            case Prc(fun) => fun(arg)(ctn)
                            case any => sys.error("Not a function designator: " + any)
                         } ) )
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

object HOF_CbVCPS_CC {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  case class Clo(bod : Imp, sen : Env) extends Imp

  type Ctn = Imp => Imp

  def apCl(prc : Imp, arg : Imp, ctn : Ctn) : Imp = prc match {
    case Clo(bod, sen) => norm(bod, arg :: sen, ctn)
    case any => sys.error("Not a function designator: " + any)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => ctn(env(ind))
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      norm( opr, env
          , clo => norm( opd, env
                       , arg => apCl(clo, arg, ctn) ) )
    case _ => imp
  }
}

****************
* Rationalized *
****************/

