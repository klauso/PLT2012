/*
* This is a substitute lecture by Yi Dai for the course //Programming
* Languages and Types// by Klaus Ostermann at the University of Marburg.
*
* The material in this lecture is loosely based on the following two papers:
*
* * Mads Sig Ager, Dariusz Biernacki, Olivier Danvy, and Jan Midtgaard. A
*   functional correspondence between evaluators and abstract machines. In
*   Dale Miller, editor, Proceedings of the Fifth ACM-SIGPLAN International
*   Conference on Principlesand Practice of Declarative Programming (PPDP'03),
*   pages 8-19. ACM Press, August 2003.
*
* * Olivier Danvy. On evaluation contexts, continuations, and the rest of the
*   computation. In Hayo Thielecke, editor, Proceedings of the Fourth ACM
*   SIGPLAN Workshop on Continuations, Technical report CSR-04-1, Department
*   of Computer Science, Queen Mary's College, pages 13-23, Venice, Italy,
*   January 2004. Invited talk.
*/

/* This lecture consists of two parts.  The first part goes from evaluators to
 * abstract machines.  The second part goes the other way around.  In the
 * first part, our object-language is the call-by-name lambda calculus.  In
 * the second part, our object-language is the call-by-value lambda calculus.
 * For both parts, we use the ||de-Bruijn-index|| notation for lambda-terms.
 * (Please find more about de-Bruijn-index notation on Wikipedia.)  Our
 * meta-language is Scala as usual.
 */

/* $ From Evaluators to Abstract Machines $
 *
 * In this part, we will look at how to derive an abstract machine, called
 * Krivine's machine, for the call-by-name lambda calculus, from a standard
 * interpreter by a series of program transformations.  An ||abstract
 * machine|| is just like a machine, but has no instruction set.  Instead, it
 * directly operates on soure terms.
 */

/* $$ Higher-Order Function $$
 *
 * This interpreter implements the call-by-name lambda calculus.  It features
 * meta-level higher-order functions in the following two senses:
 *
 * # Object-level first-class functions are implemented by meta-level
 *   first-class functions and object-level function application is
 *   implemented by meta-level function application.  Since object-level
 *   functions are higher-order, meta-level functions implementing them must
 *   also be higher-order.
 *
 * # Since {{eval}} returns such meta-level functions as results, {{eval}} is
 *   higher-order too.
 */
object HOF {
  sealed abstract class Exp
  sealed abstract class Vlu  // Value

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  case class Prc(fun : Vlu => Vlu) extends Vlu  // Procedure

  type Env = List[Vlu]

  def eval(exp : Exp, env : Env) : Vlu = exp match {
    case Var(ind) => env(ind)
    case Abs(bod) => Prc(arg => eval(bod, arg :: env))
    case App(opr, opd) => eval(opr, env) match {
      case Prc(fun) => fun(eval(opd, env))
    }
  }

  def intp(exp : Exp) : Vlu = eval(exp, Nil)
}

/* Note that in the implementation of {{HOF}}, the evaluation order of the
 * object-language depends on the evaluation order of the meta-language.  The
 * dependence manifests at {{fun(eval(opd, env))}}.  
 *
 * On one hand, if the meta-language uses call-by-value, which happens to be
 * so for Scala, the object-language is forced to be call-by-value; if instead
 * the meta-language uses call-by-name, the object-language becomes
 * call-by-name too.
 *
 * On the other hand, if the meta-language uses call-by-value but we want the
 * object-languge to be call-by-name, a special construct that can delay
 * evaluation must be introduced into the meta-language; if the meta-language
 * uses call-by-name but we want the object-language to be call-by-value, a
 * special construct that can force evaluation must be introduced into the
 * meta-language.  In either case, the meta-language must be extended, which
 * sometimes may be difficult or impossible.
 *
 * Fortunately a program transformation technique can solve both problems
 * gracefully, eliminating the evaluation-order dependence between the
 * object-language and meta-language, that is, by transforming the interpreter
 * into continuation-passing style.
 *
 * But to make life a bit easier, let us first get rid of meta-level
 * first-class functions that implement object-level first-class functions.
 */

/* $$ Closure Conversion $$
 *
 * ||Closure conversion|| converts the representation of object-level
 * first-class functions to meta-level data structures, namely ||closures||.
 * The consequences are twofold:
 *
 * # It eliminates the use of meta-level first-class functions to represent
 *   object-level first-class functions.
 *
 * # It turns meta-level higher-order functions back to first-order,
 *   particularly {{eval}}.
 * 
 * Keeping from meta-level first-class functions but with meta-level
 * first-order functions opens more choices of meta-languages for
 * implementation.  For example, a language like C that does not natively
 * support first-class functions can be used.
 *
 * After closure conversion, we have an interpreter in ||direct style||, that
 * is, not manipulating explicit continuations.
 */
object HOF_CC {
  sealed abstract class Exp
  sealed abstract class Vlu

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Vlu]

  case class Clo(bod : Exp, sen : Env) extends Vlu

  def eval(exp : Exp, env : Env) : Vlu = exp match {
    case Var(ind) => env(ind)
    case Abs(bod) => Clo(bod, env)
    case App(opr, opd) => eval(opr, env) match {
      case Clo(bod, sen) => eval(bod, eval(opd, env) :: sen)
    }
  }

  def intp(exp : Exp) : Vlu = eval(exp, Nil)
}

/* $$ Call-by-Name CPS-Transformation $$
 *
 * The problem of evaluation-order dependence between the object-language and
 * the meta-language remains in the interpreter in direct style after closure
 * conversion, as evidenced by {{eval(bod, eval(opd, env) :: sen)}}.  To solve
 * the problem without extending the meta-language, we must turn to
 * CPS-transformation.
 *
 * As to see how to implement a call-by-name language in a call-by-value
 * language without extending the meta-language, we decide our object-language
 * to be the call-by-name lambda calculus and use the ||call-by-name
 * CPS-transformation|| to transform the interpreter from direct style into
 * continuation-passing style.
 *
 * The result of the transformation has the following features:
 *
 * # The evaluation order of the object-language is call-by-name.  It no
 *   longer depends on the evaluation order of the meta-language.  Even if
 *   someday Scala switches to call-by-name, our interpreter still correctly
 *   implements the call-by-name lambda calculus.
 *
 * # The whole interpreter is tail recursive and can readily be tail-call
 *   optimized.
 */
object HOF_CC_CbNCPS {
  sealed abstract class Exp
  sealed abstract class Vlu
  sealed abstract class Cpu

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Cpu]

  case class Clo(bod : Exp, sen : Env) extends Vlu

  type Ctn = Vlu => Vlu

  case class Thk(fun : Ctn => Vlu) extends Cpu

  def eval(exp : Exp, env : Env, ctn : Ctn) : Vlu = exp match {
    case Var(ind) => env(ind) match {
      case Thk(fun) => fun(ctn)
    }
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      eval( opr, env
          , clo => clo match {
              case Clo(bod, sen) => eval(bod, Thk(ctn => eval(opd, env, ctn)) :: sen, ctn)
            } )
  }

  def intp(exp : Exp) : Vlu = eval(exp, Nil, vlu => vlu)
}

/* $$ Defunctionalization $$
 *
 * ||Defunctionalization|| is a general program transformation technique that
 * eliminates higher-order functions, by replacing the creation of
 * first-class functions with the construction of data structures and the
 * application of first-class functions with the destruction of data
 * structures.
 *
 * A program that contains higher-order functions can be defunctionalized 
 * following three steps:
 *
 * # Encoding --- Identify first-class functions in the program and classify
 *   them according to their types.  For each function type, introduce an
 *   encoding data type.  For each function instance (i.e., function of the
 *   encoded function type) introduce a constructor that will construct data
 *   of the encoding type.  Make sure that each data constructor takes
 *   arguments that have the same types as the free variables of the function
 *   instance.  The idea is that each constructor should save the values bound
 *   to the free variables of the function instance.  Encoding should not
 *   cause any informatoin loss.
 *
 * # Decoding --- For each encoding data type, define a function
 *   (conventionally called "apply") that takes one argument of the data type
 *   and the other of the argument type of the encoded function type.  This
 *   "apply" function will use pattern matching to do case analysis on its
 *   first argument in order to extract the saved values bound to the free
 *   variables of the encoded function instance.  The right-hand side of each
 *   case will be the body of the encoded function instance, with variables
 *   renamed accordingly.
 *
 * # Refactoring --- Go through the program.  When an encoded function type is
 *   met, replace it with its encoding data type.  When a function instance is
 *   met, encode it by constructing data from its free variables using the
 *   corresponding constructor.  In this way, values bound to the free
 *   variables of the function instance are saved.  Locate all the places
 *   where a function instance is applied, replacing its application with an
 *   explict call of the "apply" function on (the designator of) the function
 *   instance and its argument.
 *
 * We illustrate how to defunctionalize a higher-order program following these
 * two steps by an example.  Below is a simple higher-order program that
 * defines a function that will first add {{n}} to and then multiply by {{n}}
 * every integer in a list {{xs}}.
 */

def map(f : Int => Int, xs : List[Int]) : List[Int] = xs match {
  case Nil => Nil
  case x :: xs => f(x) :: map(f, xs)
}

def addMulInts(n : Int, xs : List[Int]) : List[Int] =
  map(x => x * n, map(x => x + n, xs))

/* Let us apply the three-step procedure to this program.
 *
 * # Encoding
 *
 *   There are two first-class functions in the program, namely {{x = > x *
 *   n}} and {{x => x + n}}.  Both are instances of the type {{Int => Int}}r.
 *   Therefore we only need to introduce one data type, call it {{IntF}}.
 *   Both functions also have {{n}} of type {{Int}} as their free variables.
 *   So we introduce two data constructors, call them {{AddN}} and {{MulN}}
 *   respectively.  Each takes an argument {{n}} of type {{Int}}.
 */
sealed abstract class IntF
case class AddN(n : Int) extends IntF
case class MulN(n : Int) extends IntF

/* # Decoding
 *
 *   Next we define the "apply" function which takes one argument of type
 *   {{IntF}} and the other argument of the argument type of the encoded
 *   function type {{Int => Int}}, that is, {{Int}}.  The "apply" function
 *   will distinguish two cases, {{MulN(n)}} or {{AddN(n)}}, and respectively
 *   add {{n}} to or multiply by {{n}} its second argument.  Note that we use
 *   the same names ("x" and "n" respectively) for the second parameter and
 *   the pattern variable of each case in {{apply}}, as those for the
 *   parameter and free variable in each encoded function instance, so that we
 *   are not concerned with variable renaming and can put the body of the
 *   encoded function instance as is directly to the right-hand side of each
 *   case.  But normally, renaming variables in the body of the encoded
 *   function instance is required, for instance, if the second function
 *   instance in our example program is {{y => y * n}} instead of {{x => x *
 *   n}}.
 */
def apply(f : IntF, x : Int) : Int = f match {
  case MulN(n) => x * n
  case AddN(n) => x + n
}

/* # Refactoring
 *
 *   Now we are ready to actually defunctionalize the original higher-order
 *   program.  First, we replace the function type {{Int => Int}} of the
 *   parameter {{f}} of {{map}} with our encoding data type {{IntF}}.  Second,
 *   we replace the two function instances {{x => x * n}} and {{x => x + n}}
 *   in the body of {{AddMulInts}} by {{MulN(n)}} and {{AddN(n)}}
 *   respectively.  Note that both functions will be bound to {{f}} and passed
 *   in to {{map}}.  In other words, where {{f}} is applied in {{map}} is
 *   where these function instances are applied.  Thus the third is to replace
 *   the application of {{f}} to {{x}} with an explicit invocation of
 *   {{apply}} on {{f}} and {{x}}.
 */
def map(f : IntF, xs : List[Int]) : List[Int] = xs match {
  case Nil => Nil
  case x :: xs => apply(f, x) :: map(f, xs)
}

def addMulInts(n : Int, xs : List[Int]) : List[Int] =
  map(MulN(n), map(AddN(n), xs))
 
/* Defunctionalization can also be applied to non-trivial higher-order
 * programs, like interpreters.
 * 
 * Actually closure conversion can be seen as a special case of
 * defunctionalization.  It is usually done before transforming the
 * interpreter into continuation-passing style to ease the whole task.  Below
 * is what we get by defunctionalizing meta-level first-class functions that
 * implement object-level first-class functions.  {{apCl}} is the "apply"
 * function.  It can be easily verified that inlining {{apCl}} gives exactly
 * the interpreter defined in {{HOF_CC}}.
 */
object HOF_DFP {
  sealed abstract class Exp
  sealed abstract class Vlu

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Vlu]

  case class Clo(bod : Exp, sen : Env) extends Vlu

  def apCl(clo : Vlu, arg : Vlu) : Vlu = clo match {
    case Clo(bod, sen) => eval(bod, arg :: sen)
  }

  def eval(exp : Exp, env : Env) : Vlu = exp match {
    case Var(ind) => env(ind)
    case Abs(bod) => Clo(bod, env)
    case App(opr, opd) => apCl(eval(opr, env), eval(opd, env))
  }

  def intp(exp : Exp) : Vlu = eval(exp, Nil)
}

/* Back to our original plan, since CPS-transformation reintroduced meta-level
 * first-class functions and in turn higher-order functions as well into the
 * closure-converted interpreter, we are going to apply defunctionalization to
 * our CPS-transformed interpreter {{HOF_CC_CbNCPS}}.  
 *
 * There are two function types, namely {{Vlu => Vlu}} for continuation and
 * {{Ctn => Vlu}} for delayed computation.  We will defunctionalize them
 * separately.  We choose to first handle {{Ctn => Vlu}}.  The other way
 * around works as well and is left as an exercise.
 */

/* $$$ Defunctionalizing Computation $$$
 *
 * For the function type {{Ctn => Vlu}}, we introduce an encoding data type
 * {{Cpu}}, the name abbreviating computation.  There is only one instance of
 * type {{Ctn => Vlu}}, that is, {{ctn => eval(opd, env, ctn)}}.  It contains
 * two free variables, namely {{opd}} of type {{Exp}} and {{env}} of type
 * {{Env}}.  Therefore we introduce one data constructor {{Thk}} that takes
 * one argument of type {{Exp}} and the other of type {{Env}}, without loss of
 * generality, named {{opd}} and {{env}} respectively.  The "apply" function,
 * called {{apCp}} is readily defined.  During refactoring, the only function
 * instance is replaced with {{Thk(opd, env)}}, and the application of the
 * encoded function {{fun(ctn)}} is replaced with an explicit invocation of
 * {{apCp}} on {{env(ind)}} which is supposed to be data encoding compuation
 * and the continuation {{ctn}}.  The result is the following interpreter.
 */
object HOF_CC_CbNCPS_DFC {
  sealed abstract class Exp
  sealed abstract class Vlu
  sealed abstract class Cpu

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Cpu]

  case class Clo(bod : Exp, sen : Env) extends Vlu

  type Ctn = Vlu => Vlu

  case class Thk(opd : Exp, den : Env) extends Cpu

  def apCp(thk : Cpu, ctn : Ctn) : Vlu = thk match {
    case Thk(opd, den) => eval(opd, den, ctn)
  }

  def eval(exp : Exp, env : Env, ctn : Ctn) : Vlu = exp match {
    case Var(ind) => apCp(env(ind), ctn)
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      eval( opr, env
          , clo => clo match {
              case Clo(bod, sen) => eval(bod, Thk(opd, env) :: sen, ctn)
            } )
  }

  def intp(exp : Exp) : Vlu = eval(exp, Nil, vlu => vlu)
}

/* $$$$ Inlining $$$$
 *
 * We can similarly inline {{apCp}}, which gives:
 */
object HOF_CC_CbNCPS_DFC_Inl {
  sealed abstract class Exp
  sealed abstract class Vlu
  sealed abstract class Cpu

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Cpu]

  case class Clo(bod : Exp, sen : Env) extends Vlu

  type Ctn = Vlu => Vlu

  case class Thk(opd : Exp, den : Env) extends Cpu

  def eval(exp : Exp, env : Env, ctn : Ctn) : Vlu = exp match {
    case Var(ind) => env(ind) match {
      case Thk(opd, den) => eval(opd, den, ctn)
    }
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      eval( opr, env
          , clo => clo match {
              case Clo(bod, sen) => eval(bod, Thk(opd, env) :: sen, ctn)
            } )
  }

  def intp(exp : Exp) : Vlu = eval(exp, Nil, vlu => vlu)
}

/* $$$ Defunctionalizing Continuation $$$
 *
 * Next we defunctionalize the function type {{Vlu => Vlu}} for continuation.
 * First, we introduce a new data type {{Ctn}}.  Second, we find that there
 * are two instances of the function type: {{clo => clo match { ... }}} and
 * {{vlu => vlu}}.  The former has three free variables: {{opd}} of type
 * {{Exp}}, {{env}} of type {{Env}} and {{ctn}} of type {{Ctn}}.  The latter
 * has no free variable.  Therefore we introduce two data constructors:
 * {{ApC}} with two parameters {{opd}} of type {{Exp}} and {{env}} of type
 * {{Env}}, {{IdC}} with no parameter.  The apply function, called {{apCt}} is
 * again easily defined.  Third, we replace the two instances {{clo => clo
 * match { ... }}} and {{vlu => vlu}} with {{ApC(opd, env, ctn)}} and
 * {{IdC()}} respectively, the application of them {{ctn(Clo(bod, env)}} with
 * an explicit invocation of {{apCt}} on {{ctn}} and {{Clo(bod, env)}}.  We
 * obtain the following interpreter without meta-level first-class functions
 * and higher-order functions.
 */
object HOF_CC_CbNCPS_DFC_Inl_DFC {
  sealed abstract class Exp
  sealed abstract class Vlu
  sealed abstract class Cpu
  sealed abstract class Ctn

  case class Var(ind : Int) extends Exp
  case class Abs(bod : Exp) extends Exp
  case class App(opr : Exp, opd : Exp) extends Exp

  type Env = List[Cpu]

  case class Clo(bod : Exp, sen : Env) extends Vlu

  case class Thk(opd : Exp, den : Env) extends Cpu

  case class ApC(opd : Exp, den : Env, ctn : Ctn) extends Ctn
  case class IdC() extends Ctn

  def apCt(ctn : Ctn, vlu : Vlu) : Vlu = ctn match {
    case ApC(opd, den, ctn) => vlu match {
      case Clo(bod, sen) => eval(bod, Thk(opd, den) :: sen, ctn)
    }
    case IdC() => vlu
  }

  def eval(exp : Exp, env : Env, ctn : Ctn) : Vlu = exp match {
    case Var(ind) => env(ind) match {
      case Thk(opd, den) => eval(opd, den, ctn)
    }
    case Abs(bod) => apCt(ctn, Clo(bod, env))
    case App(opr, opd) => eval(opr, env, ApC(opd, env, ctn))
  }

  def intp(exp : Exp) : Vlu = eval(exp, Nil, IdC())
}

/* $$$$ Refactoring $$$$
 *
 * Unifying the data structure for closure and thunk, listifying the data
 * structure for continuation, and inlining {{apCt}} gives us an
 * implementation of Krivine's machine.
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
  case class ALC(opd : Exp, env : Env, ctx : Ctx) extends Ctx
  case class ARC(clo : EVa, ctx : Ctx) extends Ctx

  def apCt(ctx : Ctx, eva : EVa) : EVa = ctx match {
    case IdC() => eva
    case ALC(opd, env, ctx) => eva match {
      case clo@Clo(_, _) => eval(opd, env, ARC(clo, ctx))
    }
    case ARC(Clo(bod, sen), ctx) => eval(bod, eva :: sen, ctx)
  }

  def eval(exp : Exp, env : Env, ctx : Ctx) : EVa = exp match {
    case Var(ind) => apCt(ctx, env(ind))
    case Abs(bod) => apCt(ctx, Clo(bod, env))
    case App(opr, opd) => eval(opr, env, ALC(opd, env, ctx))
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
    }
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil)
}

/* Call-by-Name CPS-Transformation */

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
    }
    case Abs(bod) => ctn(Prc(cmp => ctn => norm(bod, cmp :: env, ctn)))
    case App(opr, opd) =>
      norm( opr, env
          , prc => prc match {
              case Prc(fun) => fun(Cmp(ctn => norm(opd, env, ctn)))(ctn)
            } )
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

/* Defunctionalizing Procedures and Computation */

object HOF_CbNCPS_DFPC {
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
  }

  def apTh(thk : Imp, ctn : Ctn) : Imp = thk match {
    case Thk(opd, sen) => norm(opd, sen, ctn)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => apTh(env(ind), ctn)
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      norm( opr, env
          , clo => apCl(clo, Thk(opd, env), ctn) )
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

/* Defunctionalizing Continuation */

object HOF_CbNCPS_DFPC_DFC {
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
  }

  def apTh(thk : Imp, ctn : Ctn) : Imp = thk match {
    case Thk(opd, sen) => norm(opd, sen, ctn)
  }

  def apCt(ctn : Ctn, clo : Imp) : Imp = ctn match {
    case IdC() => clo
    case ApC(opd, sen, ctn) => apCl(clo, Thk(opd, sen), ctn)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => apTh(env(ind), ctn)
    case Abs(bod) => apCt(ctn, Clo(bod, env))
    case App(opr, opd) => norm(opr, env, ApC(opd, env, ctn))
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, IdC())
}

/* Refactoring */

object HOF_CbNCPS_DFP_DFC_Rfc {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  case class Clo(imp : Imp, sen : Env) extends Imp

  type Ctn = List[Imp]

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => env(ind) match {
      case Clo(opd, sen) => norm(opd, sen, ctn)
    }
    case Abs(bod) => ctn match {
      case Nil => Clo(bod, env)
      case Clo(opd, den) :: ctn => norm(bod, Clo(opd, den) :: env, ctn)
    } 
    case App(opr, opd) => norm(opr, env, Clo(opd, env) :: ctn)
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, Nil)
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
                         } ) )
  }

  def intp(imp : Imp) : Imp = norm(imp, Nil, nfd => nfd)
}

object HOF_CbVCPS_DFP {
  sealed abstract class Imp

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  case class Clo(bod : Imp, sen : Env) extends Imp

  type Ctn = Imp => Imp

  def apCl(prc : Imp, arg : Imp, ctn : Ctn) : Imp = prc match {
    case Clo(bod, sen) => norm(bod, arg :: sen, ctn)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => ctn(env(ind))
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      norm( opr, env
          , clo => norm( opd, env
                       , arg => apCl(clo, arg, ctn) ) )
  }
}

object HOF_CbVCPS_DFP_DFC {
  sealed abstract class Imp
  sealed abstract class Ctn

  case class Var(ind : Int) extends Imp
  case class Abs(bod : Imp) extends Imp
  case class App(opr : Imp, opd : Imp) extends Imp

  type Env = List[Imp]

  case class Clo(bod : Imp, sen : Env) extends Imp

  case class IdC() extends Ctn
  case class ALC(opd : Imp, den : Env, ctn : Ctn) extends Ctn
  case class ARC(clo : Imp, ctn : Ctn) extends Ctn

  def apCl(prc : Imp, arg : Imp, ctn : Ctn) : Imp = prc match {
    case Clo(bod, sen) => norm(bod, arg :: sen, ctn)
  }

  def norm(imp : Imp, env : Env, ctn : Ctn) : Imp = imp match {
    case Var(ind) => ctn(env(ind))
    case Abs(bod) => ctn(Clo(bod, env))
    case App(opr, opd) =>
      norm( opr, env
          , clo => norm( opd, env
                       , arg => apCl(clo, arg, ctn) ) )
  }
}

 ****************
 * Rationalized *
 ****************/

