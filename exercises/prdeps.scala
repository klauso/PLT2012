/* 
 * The Power and Responsibility of Direct-Environment-Passing Style
 *
 * Author: Yi Dai
 * Date: 2012-11-18
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

/*
 * (let ((x 1))
 *   (let ((f (lambda (y)
 *              (set! x (+ x y)) ) ) )
 *     (f 2)
 *     x ) )
 */

def test3 : Imp =
  Let( 'x, Nml(1)
     , Let( 'f, Lam('y, Set('x, Pls(Smb('x), Smb('y))))
          , Seq( Cmb(Smb('f), Nml(2))
               , Smb('x) ) ) )

