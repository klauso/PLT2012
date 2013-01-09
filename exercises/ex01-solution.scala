/*

Programming languages and types

Solution to exercise session A on 22.10.2012

Should be uploaded before 29.10.12, 1000 hrs.

As with lecture notes, this file can be checked and experimented with
by running the scala interpreter and typing

scala> :l A.scala


Contents
========

1. Github
2. Functions
3. Lists
4. Visitors
5. Church encoding
6. Variables in AE
7. Free variables in WAE
8. Name binding
9. Substitution
*/

/*
0. Necessary declarations from lecture notes 2-ae.scala and 3-wae.scala
*/
sealed abstract class Exp 
case class Num(n: Int) extends Exp
case class Add(lhs: Exp, rhs: Exp) extends Exp
case class Mul(lhs: Exp, rhs: Exp) extends Exp
case class Id(x: Symbol) extends Exp
case class With(x: Symbol, xdef: Exp, body: Exp) extends Exp
implicit def num2exp(n: Int) = Num(n)
implicit def sym2exp(x: Symbol) = Id(x)
type Env = Map[Symbol,Int]
case class Visitor[T](num:Int=>T, add:(T,T)=>T, mul:(T,T)=>T, id:Symbol=>T)
def foldExp[T](v: Visitor[T], e: Exp) : T = {
  e match {
    case Num(n) => v.num(n)
    case Id(x) => v.id(x)
    case Add(l,r) => v.add(foldExp(v,l), foldExp(v,r))
    case Mul(l,r) => v.mul(foldExp(v,l), foldExp(v,r))
    case With(x, xdef, body) => sys.error("AE expected, WAE encountered!")
  }
}


/*
1. Github
=========

a) Create a Github account unless you have one already: www.github.com

b) Fork the repository github.com/klauso/PLT2012

c. Edit roster.txt and append your name, account name and language
   preference for exercise sessions. Save it by a commit. Feel free to
   modify your vote through more commits later.

d. Send us your changes via a "pull request".
*/

/*
2. Functions
============
*/

// Syntax of function definition
def twice (x : Int) : Int = 2 * x

// Function as lambda-abstraction
val twice1 = (x : Int) => 2 * x

// Functions are first-class values and can be taken as arguments.
def apply_to_21(f : Int => Int) : Int = f(21)
apply_to_21(twice)
apply_to_21(twice1)

// Function-application syntax is available to all objects with an
// `apply` method. Nevertheless, only instances of subclasses of
// `Function` can be passed as a functional argument.
val twice2 = new Object { def apply(x : Int) = 2 * x }
val twice3 = new Function[Int,Int] { def apply(x : Int) = 2 * x }

twice2(21)
twice3(21)

// apply_to_21(twice2) // Type error!
apply_to_21(twice3)

// Sometices the argument type can be inferred.

// val twice4 = x => 2 * x // not enough info for type inference

val twice4 : Int => Int = x => 2 * x

apply_to_21(x => 2 * x)

// Syntactic sugar for the above
apply_to_21(2 * _)

/*
3. Lists
========
*/

// A list. No change to the values is possible after definition.
val list123 = List(1, 2, 3)

// Lists are stored as linked lists using a class :: and a class NIl.
val list123 = 1 :: 2 :: 3 :: Nil

// Note that :: is right-associative, so the above means:
val list123 = 1 :: (2 :: (3 :: Nil))

// Deconstructing a list by pattern matching
list123 match {
  case Nil     => "Leere Liste"
  case x :: xs => "Mit " + x + " angefangene Liste"
}

// a) Please write a function to calculate the sum of a list of
//    integers by pattern matching.

def sum(list : List[Int]) : Int = list match {
  case Nil     => 0
  case x :: xs => x + sum(xs)
}

// b) Write a pretty-printer for lists of integers by pattern
//    matching:
//
//    print( List(1, 2, 3) ) = "1 :: 2 :: 3 :: Nil"

def print(list : List[Int]) : String = list match {
  case Nil     => "Nil"
  case x :: xs => x + " :: " + print(xs)
}

/*
4. Visitors
===========
*/

// Cf. `foldExp` in 2-ae.scala:104,125
case class ListVisitor[T, R](nil : R, cons : (T, R) => R)

def foldList[T, R](list : List[T], visitor : ListVisitor[T, R]) : R =
  list match {
    case Nil => visitor.nil
    case head :: tail => visitor.cons(head, foldList(tail, visitor))
  }

// a) Reimplement `sum` and `print` through visitors.

val sumVisitor = new ListVisitor[Int, Int](0, _ + _)
def sum(list : List[Int]) = foldList(list, sumVisitor)

val printVisitor = new ListVisitor[Int, String]("Nil", _ + " :: " + _)
def print(list : List[Int]) = foldList(list, printVisitor)

/*
5. Church encoding
==================

Advantages of Church encoding:

1. More ways to express certain concepts

2. Implementation of language features without extending the core
   language

3. Problemsolving; the following paper for example solves the
   "expression problem" by church-encoding abstract syntax trees:

    C. d. S. Oliveira and William R. Cook:
    Extensibility for the masses---
      practical extensibility with object algebras.
    Proceedings of ECOOP: 2--27 (2012)

Feel free to suggest other justifications for Church encoding.
*/

abstract class ListC[T] { def apply[R](v : ListVisitor[T,R]) : R }

// a) Please complete the implementation of Church-encoded lists.
//    The following lecture note may be helpful:
//
//      2-ae.scala:188--198
//
//    Also recall the definition of ListVisitor:
//
//      case class ListVisitor[T, R](nil : R, cons : (T, R) => R)

def nil[T] : ListC[T] = new ListC[T] {
  def apply[R](v : ListVisitor[T, R]) : R = v.nil
}
   
def cons[T](head : T, tail : ListC[T]) = new ListC[T]{
  def apply[R](v : ListVisitor[T, R]) : R = v.cons(head, tail(v))
}
   
val list1234 = cons(1, cons(2, cons(3, cons(4, nil[Int]))))
   
def sum(listc : ListC[Int]) : Int = listc(sumVisitor)
   
def print(listc : ListC[Int]) : String = listc(printVisitor)

/*
6. Variables in AE
==================

Hint about sets in Scala:

  `Set(1, 2, 3)`     constructs a set with fixed members.
  `set1 + element`   creates a set with one element added.
  `set1 - element`   creates a set with one element removed.
  `set1 ++ set2`     computes the union of two sets.
  `set1 -- set2`     computes the difference of two sets.
*/

// Implement scala functions computing the set of variables
// that occur in an AE program.

// a) With pattern matching

def variables1(e : Exp) : Set[Symbol] = e match {
  case Num(n)        => Set()
  case Add(lhs, rhs) => variables1(lhs) ++ variables1(rhs)
  case Mul(lhs, rhs) => variables1(lhs) ++ variables1(rhs)
  case Id(x)         => Set(x)
  case With(_,_,_)   => sys.error("AE expected, WAE encountered!")
}

// b) using a visitor and the `foldExp` function

val variablesVisitor = Visitor[Set[Symbol]](
  _ => Set(), // The underscore _ denotes an ignored argument
  _ ++ _,     // The underscores denote resp. the first and second argument
  _ ++ _,     // So an underscore has many meanings and is ambiguous alone.
  x => Set(x)
)

def variables2(e : Exp) : Set[Symbol] = foldExp(variablesVisitor, e)

// c) Testcases, uncomment to execute. Feel free to add more!

assert(variables1(Add('x, 'y)) == Set('x, 'y))
assert(variables1(Mul(Add(9, 'y), Mul('x, 'y))) == Set('x, 'y))

assert(variables2('x) == Set('x))
assert(variables2(Add(Mul('x, 5), Add(4, 'x))) == Set('x))

/*
7. Free Variables in WAE
========================
*/

// a) Implement a scala function that computes the set of all free (!)
//    variables of a WAE term.

def freeVariables(wae : Exp) : Set[Symbol] = wae match {
  case Num(n)        => Set()
  case Add(lhs, rhs) => freeVariables(lhs) ++ freeVariables(rhs)
  case Mul(lhs, rhs) => freeVariables(lhs) ++ freeVariables(rhs)
  case Id(x)         => Set(x)
  case With(x, xdef, body)
    => freeVariables(xdef) ++ (freeVariables(body) - x)
}

// b) Test cases; feel free to define more.

assert(freeVariables(Id('x)) == Set('x))
assert(freeVariables(With('x, 5, Add('x, 'y))) == Set('y))

// A new test case.
// Note that due to the lack of recursion in WAE,
// the scope of 'x in With('x, xdef, body) does _not_
// extend to xdef.

assert(freeVariables(With('x, Add('x, 'y), 'x)) == Set('x, 'y))

/*
8. Name binding
===============
*/

// a) Please decide whether each occurrence of the symbols 'x, 'y
//    in the following WAE term is binding, bound or free.

With('x, 5,                   // Binding
         Add('x,              // Bound
             With('x, 3,      // Binding
                      Mul('y, // Free
                          'x) // Bound
)))

// b) Write a scala snippet where a name is shadowed. Describe the
//    scopes of the name bindings.

/* Scala snippet to explain the concept of "shadowing"
*/

// Adapted from Jonathan Brachthäuser's solution
val example = (x : Int) => (y : Int) => ((x : Int) => x + y)(2 * x)
//            [    scope of first x                               ]
//                         [       scope of y                     ]
//                                       [ scope of 2nd x ]


/*
9. Substitution
===============
*/

// a) Implement a substitution function such that evaluation via
//    call-by-name and evaluation via call-by-value always have
//    the same result (error included) on all inputs.
//
//    Hints:
//
//    - During the lecture on 22.10.12 it was mentioned
//      that renaming of variables is necessary to avoid
//      accidental name capturing.
//
//    - It is recommended to separate the substitution algorithm
//      into several helper functions.
//
//    - You are welcome to implement an idea of your own,
//      independent from the lecture and the hints here.

val randomNumberGenerator = new scala.util.Random()

// freshVariable:
// Finds a name such as 'x42 that does not occur in the set of symbols
// The second parameter `startNumber` denotes the number, say 42,
// such that the search start at the name 'x42. It has a random
// default value to speed up the search. Thus, `freshName` is no
// longer a pure function.
def freshName(
  set : Set[Symbol],
  startNumber : Int = randomNumberGenerator.nextInt.abs
) : Symbol = {
  val name = Symbol("x" + startNumber)
  if (set.contains(name)) freshName(set) else name
}

def subst(e : Exp, i : Symbol, v : Exp) : Exp = e match {
    case Num(n)    => e
    case Id(x)     => if (x == i) v else e
    case Add(l, r) => Add(subst(l, i, v), subst(r, i, v))
    case Mul(l, r) => Mul(subst(l, i, v), subst(r, i, v))
    // Handle shadowing perfectly.
    // If `x` occurs free in `v`,
    // then to avoid accidental name capturing,
    // we must rename all free occurrences of `x` in `body`
    // to some fresh name that is free in neither `body` nor `v`
    // before we substitute `i` with `v` in `body`.
    case With(x, xdef, body)
      => if (x == i)
           With(x, subst(xdef, i, v), body)
         else {
           val free_in_v = freeVariables(v)
           if (free_in_v.contains(x)) {
             val fresh_name = freshName(free_in_v ++ freeVariables(body))
             With(fresh_name,
                  subst(xdef, i, v),
                  subst(subst(body, x, Id(fresh_name)), i, v))
           }
           else
             With(x, subst(xdef, i, v), subst(body, i, v))
         }
}

def eval_by_value(e: Exp) : Int = e match {
  case Num(n) => n
  case Id(x) => sys.error("Free variable: "+x)
  case Add(l,r) => eval_by_value(l) + eval_by_value(r)
  case Mul(l,r) => eval_by_value(l) * eval_by_value(r)
  case With(x, xdef, body) =>
    eval_by_value(subst(body, x, Num(eval_by_value(xdef))))
}

def eval_by_name(e: Exp) : Int = e match {
  case Num(n) => n
  case Id(x) => sys.error("Free variable: "+x)
  case Add(l,r) => eval_by_name(l) + eval_by_name(r)
  case Mul(l,r) => eval_by_name(l) * eval_by_name(r)
  case With(x, xdef, body) =>
    eval_by_name(subst(body, x, xdef))
}

// b) Test cases. Feel free to add more.

/* Contributed by Jonathan Brachthäuser

With x = y
  With y = 1
    x 


With x = 4
  With x = 5
    x

With x = 4
  With y = x + x   // 1
    With x = 5     
      y            // 2

*/
val err_exp1 = With('x, 'y, With('y, 1, 'x))

def test_v1 = eval_by_value(err_exp1)
def test_n1 = eval_by_name(err_exp1)

// Both tests should produce the error "Free variable: y"
// test_v1
// test_n1

val example1 = With('x, 4, With('x, 5, 'x))
assert(eval_by_value(example1) == eval_by_name(example1))
  
val example2 = With('x, 4, With('y, Add('x, 'x), With('x, 5, 'y)))
assert(eval_by_value(example2) == eval_by_name(example2))
