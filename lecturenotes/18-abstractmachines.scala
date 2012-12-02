/* Higher-Order Function */

object HOF1 {
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
    }
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil)
}

object HOF2 {
  sealed abstract class Exp
  sealed abstract class Val

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  case class Prc(fun : Val => Val) extends Val

  type Env = List[Val]

  def eval(exp : Exp, env : Env) : Val = exp match {
    case Var(ind) => env(ind)
    case Abs(bod) => Prc(arg => eval(bod, arg :: env))
    case App(opr, opd) => eval(opr, env) match {
      case Prc(fun) => fun(eval(opd, env))
    }
  }

  def intp(exp : Exp) : Val = eval(exp, Nil)
}


/* CPS Transformation */

object CbNCPS1 {
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

object CbNCPS2 {
  sealed abstract class Exp
  sealed abstract class Val

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Ctn = Val => Val
  case class Prc(fun : Val => Ctn => Val) extends Val
  case class Prm(fun : Ctn => Val) extends Val

  type Env = List[Val]

  def eval(exp : Exp, env : Env, ctn : Ctn) : Val = exp match {
    case Var(ind) => env(ind) match {
      case Prm(fun) => fun(ctn)
      case prc => ctn(prc)
    }
    case Abs(bod) => ctn(Prc(prm => ctn => eval(bod, prm :: env, ctn)))
    case App(opr, opd) =>
      eval( opr, env
          , prc => prc match {
              case Prc(fun) => fun(Prm(ctn => eval(opd, env, ctn)))(ctn)
            } )
  }

  def intp(exp : Exp) : Val = eval(exp, Nil, vlu => vlu)
}

object CbNCPS3 {
  sealed abstract class Exp
  sealed abstract class Val
  sealed abstract class Prm

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Ctn = Val => Val
  case class Prc(fun : Prm => Ctn => Val) extends Val

  case class Thk(fun : Ctn => Val) extends Prm

  type Env = List[Prm]

  def eval(exp : Exp, env : Env, ctn : Ctn) : Val = exp match {
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

  def intp(exp : Exp) : Val = eval(exp, Nil, vlu => vlu)
}

object CbVCPS1 {
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
          , prc => prc match {
              case Prc(fun) => norm(opd, env, arg => fun(arg)(ctn))
            } )
    case _ => imp
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

object CbVCPS2 {
  sealed abstract class Exp
  sealed abstract class Val

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Ctn = Val => Val
  case class Prc(fun : Val => Ctn => Val) extends Val

  type Env = List[Val]

  def eval(exp : Exp, env : Env, ctn : Ctn) : Val = exp match {
    case Var(ind) => ctn(env(ind))
    case Abs(bod) => ctn(Prc(arg => ctn => eval(bod, arg :: env, ctn)))
    case App(opr, opd) =>
      eval( opr, env
          , prc => prc match {
              case Prc(fun) => eval(opd, env, arg => fun(arg)(ctn))
            } )
  }

  def intp(exp : Exp) : Val = eval(exp, Nil, vlu => vlu)
}


/* Defunctionalization */

/* Direct */

object CbNCPS_DF1 {
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

/*
 * Two steps:
 *
 * 1. Converting to closures
 */

object CC_CbNCPS3 {
  sealed abstract class Exp
  sealed abstract class Val
  sealed abstract class Prm

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  case class Clo(bod : Exp, env : Env) extends Val

  type Ctn = Val => Val
  case class Thk(fun : Ctn => Val) extends Prm

  type Env = List[Prm]

  def eval(exp : Exp, env : Env, ctn : Ctn) : Val = exp match {
    case Var(ind) => env(ind) match {
      case Thk(fun) => fun(ctn)
    }
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      eval( opr, env
          , prc => prc match {
              case Clo(bod, sen) => eval(bod, Thk(ctn => eval(opd, env, ctn)) :: sen, ctn)
            } )
  }

  def intp(exp : Exp) : Val = eval(exp, Nil, vlu => vlu)
}

/* 2. Defunctionalizing continuation */

object CC_CbNCPS_DF3 {
  sealed abstract class Exp
  sealed abstract class Val
  sealed abstract class Prm
  sealed abstract class Ctn

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Prm]

  case class Clo(bod : Exp, env : Env) extends Val

  case class Thk(opd : Exp, env : Env) extends Prm

  case class IdC() extends Ctn
  case class ApC(opd : Exp, env : Env, ctn : Ctn) extends Ctn

  def apPm(prm : Prm, ctn : Ctn) : Val = prm match {
    case Thk(opd, env) => eval(opd, env, ctn)
  }
  
  def cont(ctn : Ctn, arg : Val) : Val = ctn match {
    case IdC() => arg
    case ApC(opd, env, ctn) => arg match {
      case Clo(bod, sen) => eval(bod, Thk(opd, env) :: sen, ctn)
    }
  }

  def eval(exp : Exp, env : Env, ctn : Ctn) : Val = exp match {
    case Var(ind) => apPm(env(ind), ctn)
    case Abs(bod) => cont(ctn, Clo(bod, env))
    case App(opr, opd) => eval(opr, env, ApC(opd, env, ctn))
  }

  def intp(exp : Exp) : Val = eval(exp, Nil, IdC())
}

