Programming Languages and Types

Exercise session F on 26.11.2012

Hand in

- anytime
- as a single .scala or .pdf file to pllecture@informatic, or
- in paper form during lectures or exercise sessions.



I. First-class continuations
============================

In which system can one implement a `letcc` construct? Justify your
answer with brief explanations or implementation ideas.

0. Direct-style interpreter, direct-style programme.

1. Direct-style interpreter, CPS-transformed programme.

2. CPS-transformed interpreter, direct-style programme.

3. CPS-transformed interpreter, CPS-transformed programme.



II. Defunctionalisation
=======================

1. Explain what defunctionalization is and what it is good for.

2. Lambda-lift the following program:
    
    def fold[A,B](f: (A, B) => A, e: A, l: List[B]): A = 
      l match {
        case Nil => e
        case x :: xs => fold(f, f((e, x)), xs)
      }
    
    fold((x, y) => (x + y) / 2, 1, List(1, 2, 3, 4, 5))

3. Defunctionalise the resulting program.

5. Repeat steps 2--4 for the following use of fold.

    fold((f: Int => Int, g: Int => Int) => (z: Int) => f(g(z)),
         (z: Int) => z,
         List(x => x+1, x => x+2, x => x-1, x => x*2))
