/* 
 * The Power and Responsibility of Environment-Passing Style
 *
 * Author: Yi Dai
 * Date: 2012-11-17
 */

sealed abstract class Imp
case class Nml(num : Int) extends Imp
case class Smb(nom : Symbol) extends Imp
case class Pls(lhs : Imp, rhs : Imp) extends Imp
case class If0(cnd : Imp, csq : Imp, alt : Imp) extends Imp
case class Lam(prm : Symbol, bod : Imp) extends Imp
case class Cmb(opr : Imp, opd : Imp) extends Imp
case class Seq(zth : Imp, fst : Imp) extends Imp
case class Set(nom : Symbol, dfn : Imp) extends Imp

type Env = List[(Symbol, Imp)]

case class Clo(env : Env, prm : Symbol, bod : Imp) extends Imp

def Let(nom : Symbol, dfn : Imp, bod : Imp) : Imp = Cmb(Lam(nom, bod), dfn)

def isNormal(imp : Imp) : Boolean = imp match {
  case Nml(_) => true
  case Clo(_, _, _) => true
  case _ => false
}

type Cnt = (Imp, Env) => (Imp, Env)

def lookup[A, B](a : A, al : List[(A, B)]) : B = {
  if (al.isEmpty)
    sys.error("not found: " + a)
  else if (((al.head)_1) == a)
    (al.head)_2
  else
    lookup(a, al.tail)
}
 
def update[A, B](a : A, b : B, al : List[(A, B)]) : List[(A, B)] = {
  if (al.isEmpty)
    List()
  else if (((al.head)_1) == a)
    (a, b) :: al.tail
  else
    al.head :: update(a, b, al.tail)
}

def norm(imp : Imp, env : Env, cnt : Cnt) : (Imp, Env) = imp match {
  case Nml(_) => cnt(imp, env)
  case Clo(_, _, _) => cnt(imp, env)
  case Smb(nom) => cnt(lookup(nom, env), env)
  case Pls(lhs, rhs) =>
    norm( lhs, env
        , (nf0, env0) => nf0 match {
            case Nml(num0) =>
              norm( rhs, env0
                  , (nf1, env1) => nf1 match {
                      case Nml(num1) => cnt(Nml(num0 + num1), env1)
                      case _ => sys.error("not a number designator: " + rhs)
                    } )
            case _ => sys.error("not a number designator: " + lhs)
          } )
  case If0(cnd, csq, alt) =>
    norm( cnd, env
        , (nf0, env0) => nf0 match {
            case Nml(0) => norm( csq, env0
                               , (nf1, env1) => cnt(nf1, env1) )
            case Nml(_) => norm( alt, env0
                               , (nf2, env2) => cnt(nf2, env2) )
            case _ => sys.error("not a number designator: " + cnd)
          } )
  case Lam(prm, bod) => cnt(Clo(env, prm, bod), env)
  case Cmb(opr, opd) =>
    norm( opr, env
        , (nf0, env0) => nf0 match {
            case Clo(cenv, prm, bod) =>
              norm( opd, env0
                  , (nf1, env1) =>
                      norm( bod, (prm, nf1) :: cenv
                          , (nf, lenv) =>
                              cnt( nf
                                 , opr match {
                                     case Smb(nom) => update(nom, Clo(lenv.tail, prm, bod), env1)
                                     case _ => env1
                                   } ) ) )
            case _ => sys.error("not a function designator: " + opr)
          } )
  case Seq(zth, fst) =>
    norm( zth, env
        , (_, env0) =>
            norm( fst, env0
                , (nf1, env1) => cnt(nf1, env1) ) )
  case Set(nom, dfn) =>
    norm( dfn, env
        , (nf, env0) => cnt(nf, update(nom, nf, env0)) )
}

def emEnv : Env = List()
def idCnt : Cnt = (x, y) => (x, y)

/*
 * (let ((x 1))
 *   (+ (let ((x 2)) x)
 *      x ) )
 */

def test0 : Imp =
  Let( 'x, Nml(1)
     , Pls( Let('x, Nml(2), Smb('x)) 
          , Smb('x) ) )

/*
 * (let ((x 1))
 *   (let ((f (lambda (y) (+ x y))))
 *     (set! x 2)
 *     (f 3) ) )
 */

def test1 : Imp =
  Let( 'x, Nml(1)
     , Let( 'f, Lam('y, Pls(Smb('x), Smb('y)))
          , Seq( Set('x, Nml(2))
               , Cmb(Smb('f), Nml(3)) ) ) )

/*
 * (let ((counter (lambda (y)
 *                  (let ((z y))
 *                    (lambda (s)
 *                      (if (= s 0)
 *                          z
 *                          (begin (set! z (+ z s))
 *                                 z ) ) ) ) ) ) )
 *    (let ((count (counter 0)))
 *      (count 1)
 *      (count 2) ) )
 */

def test2 : Imp =
  Let( 'counter, Lam('y, Let( 'z, Smb('y)
                            , Lam('s, If0( Smb('s)
                                         , Smb('z)
                                         , Seq( Set('z, Pls(Smb('z), Smb('s)))
                                              , Smb('z) ) ) ) ) )
     , Let( 'count, Cmb(Smb('counter), Nml(0))
          , Seq( Cmb(Smb('count), Nml(1))
               , Cmb(Smb('count), Nml(2)) ) ) )

