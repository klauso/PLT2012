Programming Languages and Types

Exercise session I on 17.12.2012

Hand in

- anytime
- as a single .scala file to pllecture@informatik

Solution will be posted before 14.01.13, 1400 hrs.

The tutor shall give feedback to each submission, without giving
points. Homework does not count toward course requirement. Do them for
your own benefit.

While everyone should write their own solution, it is recommended to
work face-to-face in small groups.


I. Modular Semantics
====================

Copy
[20-normalization.scala]
(https://github.com/klauso/PLT2012/blob/master/lecturenotes/20-normalization.scala).
Observe the similarities between `object Evaluation` and `object Evaluation2`.
Try to write one evaluator to do the jobs of both by abstracting
over `Semantics` and `Semantics2`. The following interface is one possibility.

    trait Semantics[Domain] { def ... }
    
    object Domain1 {
      type Domain = Env => Value
      type Env = Map[Symbol, Value]
      abstract sealed class Value
    }
    
    object Semantics1 extends Semantics[Domain1.Domain] {
      import Domain1._
      def ...
    }

If you did _not_ follow the above approach and
ran into `error: illegal dependent method type`, try starting Scala-interpreter thus:

    scala -Ydependent-method-types

