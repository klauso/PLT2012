Programming Languages and Types

Exercise session G on 03.12.2012

Hand in

- anytime
- as a single .scala or .pdf file to pllecture@informatic, or
- in paper form during lectures or exercise sessions.



I. First-class continuations
============================

In which system can one implement a `letcc` construct? Justify your
answer with brief explanations or implementation ideas.

a.  Direct-style interpreter, direct-style programme.

b.  Direct-style interpreter, CPS-transformed programme.

c.  CPS-transformed interpreter, direct-style programme.

d.  CPS-transformed interpreter, CPS-transformed programme.



II. Defunctionalisation
=======================

a.  Explain what defunctionalization is and what it is good for.

b.  Lambda-lift the following program:
    
    def fold[A,B](f: (A, B) => A, e: A, l: List[B]): A = 
      l match {
        case Nil => e
        case x :: xs => fold(f, f((e, x)), xs)
      }
    
    fold((x, y) => (x + y) / 2, 1, List(1, 2, 3, 4, 5))

c.  Defunctionalise the resulting program.

d.  Repeat steps 2--4 for the following use of fold.

    fold((f: Int => Int, g: Int => Int) => (z: Int) => f(g(z)),
         (z: Int) => z,
         List(x => x+1, x => x+2, x => x-1, x => x*2))
