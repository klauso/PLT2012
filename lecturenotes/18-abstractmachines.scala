/*
* This lecture note by Yi Dai is loosely based on the paper
*
*   //A Functional Correspondence between Evaluators and Abstract Machines//
*
* by Olivier Danvy et al.
*/

/* = From Evaluators to Abstract Machines = */

/* == Higher-Order Function == */

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
    case Abs(bod) => Prc(thk => eval(bod, thk :: env))
    case App(opr, opd) => eval(opr, env) match {
      case Prc(fun) => fun(Prm(() => eval(opd, env)))
    }
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil)
}

/* == Closure Conversion == */

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

/* === Inlining === */

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

/* == Call-by-Name Continuation-Passing-Style Transformation == */

object HOF_CC_CbNCPS {
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

/* == Defunctionalization == */

object HOF_CC_CbNCPS_DF {
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

/* === Inlining === */

object KAM {
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
  case class ApC(opd : Exp, sen : Env, ctn : Ctn) extends Ctn

  def eval(exp : Exp, env : Env, ctn : Ctn) : EVa = exp match {
    case Var(ind) => env(ind) match {
      case Thk(opd, env) => eval(opd, env, ctn)
    }
    case Abs(bod) => ctn match {
      case IdC() => Clo(bod, env)
      case ApC(opd, sen, ctn) => eval(bod, Thk(opd, sen) :: env, ctn)
    }
    case App(opr, opd) => eval(opr, env, ApC(opd, env, ctn))
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil, IdC())
}

/* == Krivine's Abstract Machine == */

/* = From Abstract Machines to Evaluators */

/* == The CEK Machine == */

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

/* == Refunctionalization == */

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

/* == Direct-Style Transformation == */

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
    case App(opr, opd) => {
      val clo : EVa = eval(opr, env)
      val arg : EVa = eval(opd, env)
      clo match {
        case Clo(bod, sen) => eval(bod, arg :: sen)
      }
    }
  }

  def intp(exp : Exp, env : Env) : EVa = eval(exp, Nil)
}

/* == Higher-Order-Function Conversion == */

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
















/********************************** Deprecated ******************************

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
    case App(opr, opd) => {
      val prc : Imp = norm(opr, env) 
      val arg : Img = norm(opd, env)
      prc match {
        case Prc(fun) => fun(arg)
      }
    }
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil)
}

/* == Call-by-Value Continuation-Passing-Style Transformation == */

object HOF_CbVCPS {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp
  type Ctn = Imp => Imp
  case class Prc(fun : Imp => Ctn => Imp) extends Imp

  type Env = List[Imp]

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => ctn(env(ind))
    case Abs(bod) => ctn(Prc(arg => ctn => norm(bod, arg :: env, ctn)))
    case App(opr, opd) =>
      norm( opr, env
          , prc => norm( opd, env
                       , arg => prc match {
                            case Prc(fun) => fun(arg)(ctn)
                         } ) )
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

/* == Closure Conversion == */

object HOF_CbVCPS_CC {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp
  type Ctn = Imp => Imp
  case class Clo(bod : Imp, sen : Env) extends Imp

  type Env = List[Imp]

  def appl(prc : Imp, arg : Imp, ctn : Ctn) : Imp = prc match {
    case Clo(bod, sen) => norm(bod, arg :: sen, ctn)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => ctn(env(ind))
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      norm( opr, env
          , prc => norm( opd, env
                       , arg => appl(prc, arg, ctn) ) )
  }
}



object HOF_CbNCPS_DF {
  sealed abstract class Imp
  sealed abstract class Ctn

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp
  type Env = List[Imp]
  case class Clo(bod : Imp, env : Env) extends Imp
  case class Thk(opd : Imp, env : Env) extends Imp
  case class Sbs(bod : Imp, env : Env, prm : Imp) extends Imp

  case class IdC() extends Ctn
  case class ApC(opd : Imp, env : Env, ctn : Ctn) extends Ctn

  def apPc(prc : Imp, prm : Imp) : Imp = prc match {
    case Clo(bod, env) => Sbs(bod, env, prm)
  }

  def apPm(prm : Imp, ctn : Ctn) : Imp = prm match {
    case Thk(opd, env) => norm(opd, env, ctn) 
    case Sbs(opd, env, prm) => norm(opd, prm :: env, ctn)
  }

  def cont(ctn : Ctn, prc : Imp) : Imp = ctn match {
    case IdC() => prc
    case ApC(opd, env, ctn) => apPm(apPc(prc, Thk(opd, env)), ctn)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => env(ind) match {
      case prm@Thk(_, _) => apPm(prm, ctn)
      case prc@Clo(_, _) => cont(ctn, prc)
    }
    case Abs(bod) => cont(ctn, Clo(bod, env))
    case App(opr, opd) => norm(opr, env, ApC(opd, env, ctn))
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, IdC())
}

object HOF_CbNCPS {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp
  type Ctn = Imp => Imp
  case class Prc(fun : Imp => Ctn => Imp) extends Imp
  case class Prm(fun : Ctn => Imp) extends Imp

  type Env = List[Imp]

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => env(ind) match {
      case Prm(fun) => fun(ctn)
      case prc => ctn(prc)
    }
    case Abs(bod) => ctn(Prc(prm => ctn => norm(bod, prm :: env, ctn)))
    case App(opr, opd) =>
      norm( opr, env
          , prc => prc match {
              case Prc(fun) => fun(Prm(ctn => norm(opd, env, ctn)))(ctn)
            } )
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

object HOF_CC_CbNCPS {
  sealed abstract class Exp
  sealed abstract class EVa
  sealed abstract class Cpu

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Ctn = EVa => EVa
  case class Prc(fun : Prm => Ctn => EVa) extends EVa

  case class Thk(fun : Ctn => EVa) extends Prm

  type Env = List[Prm]

  def eval(exp : Exp, env : Env, ctn : Ctn) : EVa = exp match {
    case Var(ind) => env(ind) match {
      case Thk(fun) => fun(ctn)
    }
    case Abs(bod) => ctn(Prc(prm => ctn => eval(bod, prm :: env, ctn)))
    case App(opr, opd) =>
      eval( opr, env
          , prc => prc match {
              case Prc(fun) => fun(Thk(ctn => eval(opd, env, ctn)))(ctn)
            } )
  }

  def intp(exp : Exp) : EVa = eval(exp, Nil, vlu => vlu)
}

*******************************************************************************/
