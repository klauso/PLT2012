/* 
 * The Power and Limit of Continuative-Environment-Passing Style
 *
 * Author: Yi Dai
 * Date: 2012-11-25
 */

sealed abstract class Imp
case class Nml(num : Int) extends Imp
case class Var(nom : Symbol) extends Imp
case class Add(lhs : Imp, rhs : Imp) extends Imp
case class If0(cnd : Imp, csq : Imp, alt : Imp) extends Imp
case class Lam(prm : Symbol, bod : Imp) extends Imp
case class Rdx(opr : Imp, opd : Imp) extends Imp
case class Seq(zth : Imp, fst : Imp) extends Imp
case class Set(nom : Symbol, dfn : Imp) extends Imp

type Env = List[(Symbol, Imp)]

case class Clo(env : Env, prm : Symbol, bod : Imp) extends Imp

def Let(nom : Symbol, dfn : Imp, bod : Imp) : Imp = Rdx(Lam(nom, bod), dfn)

def isNormal(imp : Imp) : Boolean = imp match {
  case Nml(_) => true
  case Clo(_, _, _) => true
  case _ => false
}

type Cnt = (Imp, Env) => (Imp, Env)

def lookup[A, B](a : A, al : List[(A, B)]) : B = {
  if (al.isEmpty)
    sys.error("no association found for: " + a)
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
  case Var(nom) => cnt(lookup(nom, env), env)
  case Add(lhs, rhs) =>
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
  case Rdx(opr, opd) =>
    norm( opr, env
        , (nf0, env0) => nf0 match {
            case Clo(cenv, prm, bod) =>
              norm( opd, env0
                  , (nf1, env1) =>
                      norm( bod, (prm, nf1) :: cenv
                          , (nf, lenv) =>
                              cnt(nf, env1) ) )
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

val emEnv : Env = List()
val idCnt : Cnt = (x, y) => (x, y)

/* Power */

/*
 * (let ((x 1))
 *   (+ (let ((x 2)) x)
 *      x ) )
 */

val test0 : Imp =
  Let( 'x, Nml(1)
     , Add( Let('x, Nml(2), Var('x)) 
          , Var('x) ) )

/*
 * (let ((x 1))
 *   (set! x 2)
 *   (+ x 3) )
 */

val test1 : Imp =
  Let( 'x, Nml(1)
     , Seq( Set('x, Nml(2))
          , Add(Var('x), Nml(3)) ) )

/* Limit */

/*
 * (let ((x 1))
 *   (let ((f (lambda (y) (+ x y))))
 *     (set! x 2)
 *     (f 3) ) )
 */

val test2 : Imp =
  Let( 'x, Nml(1)
     , Let( 'f, Lam('y, Add(Var('x), Var('y)))
          , Seq( Set('x, Nml(2))
               , Rdx(Var('f), Nml(3)) ) ) )

/*
 * (let ((count (let ((counter 0))
 *                (lambda (s)
 *                  (begin (set! counter (+ counter s))
 *                         counter ) ) ) ) )
 *   (begin (count 1)
 *          (count 2) ) )
 */

val test3 : Imp =
  Let( 'count, Let( 'counter, Nml(0)
                  , Lam('s, Seq( Set('counter, Add(Var('counter), Var('s)))
                               , Var('counter) ) ) )
     , Seq( Rdx(Var('count), Nml(1))
          , Rdx(Var('count), Nml(2)) ) )

/*
 * (let ((x 1))
 *   (let ((f (lambda (y)
 *              (set! x (+ x y)) ) ) )
 *     (f 2)
 *     x ) )
 */

val test4 : Imp =
  Let( 'x, Nml(1)
     , Let( 'f, Lam('y, Set('x, Add(Var('x), Var('y))))
          , Seq( Rdx(Var('f), Nml(2))
               , Var('x) ) ) )

