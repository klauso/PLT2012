/*
Programming languages and types

Exercise session C on 05.11.2012

Hand in
   - anytime
   - as a single .scala file
   - by E-Mail to pllecture@informatik

Solution will be posted before 12.11.12, 1000 hrs.

Please feel free to contribute to the discussion in German. Cai will
likely understand you if you speak slowly and clearly.

The tutor shall give feedback to each submission, without giving
points. Homework does not count toward course requirement. Do them for
your own benefit.

While everyone should write their own solution, it is recommended to
work face-to-face in small groups. As with lecture notes, this file
can be checked and experimented with by running the scala interpreter
and typing

scala> :l A.scala


Contents
========

1. Short questions
2. If0 in Scala
3. DIY infinite lists
*/

/*
1. Short questions
==================

Give answers in 1 or 2 sentences to the following:

a) In the environment-based interpreted we introduced closures. 
   What is a closure? What do we need them for?


b) Why did we not need closures in the substitution-based interpreter?


c) Why did we not need closures in the environment-based F1WAE
   interpreter?


*/


/*
2. If0 in Scala
===============
*/

// Let us implement `if0` through a function.

def if0(
  condition   : Int,
  true_value  : Int,
  false_value : Int
) : Int = if (condition == 0) true_value else false_value

// Do not modify the factorial function!

def factorial(n : Int) : Int = if0(n, 1, n * factorial(n - 1))

// The call
//
//   factorial(5)
//
// fails in the Scala interpreter with a stack-overflow-error.
//
// a) Erklären Sie, warum.

/*
...
*/


// b) Please modify _only_ the definition of the function `if0`
//    so that `factorial(n)` computes n!.
//
//    Hint: The Scala Language Specification Version 2.9
//          Section 4.6.1
//
//          http://www.scala-lang.org/docu/files/ScalaReference.pdf


// c) Test cases. Uncomment to execute.

/*
assert(
List(0, 1, 2, 3,  4,   5,   6,    7,     8,      9).map(factorial) ==
List(1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880))
*/


/*
3. DIY infinite lists
=====================
*/

// a) Read the implementation of lazy lists below.
//    Try to understand, from the sample function
//
//      LazyList[T].toString
//
//    the meaning of each parameter of `LazyList[T].apply[R]`.
//    Explain how one is supposed to use such a lazy list.
//
//    Hint: Do exercise 2 first.

/*
...
*/

abstract class LazyList[T] {
  def apply[R](nil : => R, cons : (T, => LazyList[T]) => R) : R

  // Inspired by Tobias Weber's solution to exercise sheet A
  override def toString = this(
    "Nil",
    (head, tail) => "%s :: %s".format(head.toString, tail.toString)
  )
}

def nil[T] = new LazyList[T] {
  def apply[R](nil_val : => R, cons : (T, => LazyList[T]) => R) = nil_val
}

def cons[T](head : T, tail : => LazyList[T]) = new LazyList[T] {
  def apply[R](nil_val : => R, cons_function : (T, => LazyList[T]) => R)
    = cons_function(head, tail)
}

val list1234 = cons(1, cons(2, cons(3, cons(4, nil[Int]))))


// b) Write a `map` function that applies the first functional
//    parameter `f` to each element of the second parameter `list`
//    to produce a list of results.

def map[T, R](f : T => R, list : LazyList[T]) : LazyList[R]
  = sys.error("Implement me!")

// A test. Uncomment to run.

// assert(map[Int, Int](x => x * x, list1234).toString ==
// "1 :: 4 :: 9 :: 16 :: Nil")


// b) Write the `take` function that returns a lazy list
//    consisting of the first `n` elements of the second
//    argument.

def take[T](n : Int, list : LazyList[T]) : LazyList[T]
  = sys.error("Implement me!")

def ones : LazyList[Int] = cons(1, ones)

// Tests. Uncomment to run.

// assert(take(5, ones).toString == "1 :: 1 :: 1 :: 1 :: 1 :: Nil")
// assert(take(2, map[Int, Int](_ + 1, ones)).toString == "2 :: 2 :: Nil")


// c) Implement `ints_from(n)` to return the infinite list
//
//      (n, n + 1, n + 2, ...)

def ints_from(n : Int) : LazyList[Int] = sys.error("Implement me!")

def nats : LazyList[Int] = ints_from(1)


// d) [Hard] Write the `zip_with` function that takes a function `f`
//    and two lists as arguments and returns the list of results
//    of applying `f` to each pair of corresponding elements in the
//    two lists.

def zip_with[S, T, R](
  f      : (S, T) => R,
  list_s : LazyList[S],
  list_t : LazyList[T]
) : LazyList[R] = sys.error("Implement me!")

// assert(take(10, zip_with[Int, Int, Int](_ * _, nats, nats)).toString ==
// "1 :: 4 :: 9 :: 16 :: 25 :: 36 :: 49 :: 64 :: 81 :: 100 :: Nil")


// e) Write the infinite list of factorials using `zipWith` and `nats`.

def factorials : LazyList[Int]
  = sys.error("Implement me!")

// assert(take(10, factorials).toString ==
// "1 :: 1 :: 2 :: 6 :: 24 :: 120 :: 720 :: 5040 :: 40320 :: 362880 :: Nil")


// f) Implement `is_empty`, which returns true if and only if
//    its argument is an empty lazy list.

def is_empty[T](list : LazyList[T]) : Boolean
  = sys.error("Implement me!")


// g) Write a function to compute the last element of a lazy
//    list using `is_empty`.
//
//    Open problem: Is it possible to write `last` without `is_empty`?

def last[T](list : LazyList[T]) : T
  = list(
      sys.error("Empty list has no last element"),
      (head, tail) => if (is_empty(tail)) head else last(tail)
    )

// assert(last(list1234) == 4)


// g) Implement the `filter` function that returns a list
//    of elements of the second argument that pass the test
//    of the first argument.

def filter[T](test : T => Boolean, list : LazyList[T]) : LazyList[T]
  = sys.error("Implement me!")

// assert(take(5, filter[Int](_ % 2 == 1, nats)).toString ==
// "1 :: 3 :: 5 :: 7 :: 9 :: Nil")


// h) Write down the infinite list of prime numbers.
//    You saw a Haskell version briefly during the lecture
//    on 01.11.2012.

def primes : LazyList[Int] = sys.error("Implement me!")

// assert(last(take(100, primes)) == 541)

// Closing remark
//
// If you would like to use lazy lists for every-day computation,
// know that it is a part of Scala's standard library and its
// name is `Stream`.
//
// http://www.scala-lang.org/api/current/scala/collection/immutable/Stream.html
