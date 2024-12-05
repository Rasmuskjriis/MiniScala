package miniscala

object Week12 {

  sealed abstract class List[+T] {
    def length(): Int = this match {
      case Nil => 0
      case Cons(_, ys) => 1 + ys.length()
    }
  }
  case object Nil extends List[Nothing]
  case class Cons[T](x: T, xs: List[T]) extends List[T]

  abstract class Comparable[T] { // in real Scala code, this would be a “trait”, not an abstract class
    /** Returns <0 if this<that, ==0 if this==that, and >0 if this>that */
    def compareTo(that: T): Int
  }

  class Student(val id: Int) extends Comparable[Student] {
    def compareTo(that: Student) = this.id - that.id
  }

  def ordered[T <: Comparable[T]](list: List[T]): Boolean = list match {
    case Cons(_, Nil) => true
    case Cons(x, xs) =>
      val lowerVal: T = x
      val higherVal: T = xs match {
        case Nil => throw RuntimeException()
        case Cons(y, ys) => y
      }
      if (lowerVal.compareTo(higherVal) <= 0) ordered(xs) else false
  }

  def merge[T <: Comparable[T]](xs: List[T], ys: List[T]): List[T] = {
    if (!(ordered(xs) && ordered(ys))) throw RuntimeException("Invalid lists: Both list must be ordered")
    xs match {
      case Nil => ys
      case Cons(z, zs) =>
        ys match {
          case Nil => xs
          case Cons(a, as) => if (z.compareTo(a) <= 0) Cons(z, merge(zs, ys)) else Cons(a, merge(xs, as))
        }
    }
  }

  def mergeSort[T <: Comparable[T]](xs: List[T]): List[T] = {
    val n = xs.length() / 2
    if (n == 0) xs
    else {
      val (left, right) = split(xs, n)
      merge(mergeSort(left), mergeSort(right))
    }
  }

  def split[T <: Comparable[T]](xs: List[T], n: Int): (List[T], List[T]) = xs match {
    case Nil =>
      throw RuntimeException("Invalid number: The number must not be smaller than zero or bigger than the length of the list")
    case Cons(y, ys) => if (n == 0) (Nil, xs) else {
      val (list1, list2) = split(ys, n - 1)
      (Cons(y, list1), list2)
    }
  }
}



object Exercise122 {

  def main(args: Array[String]): Unit = {

    /**
     * Lists.
     */
    sealed abstract class List[+T] {

      def filter(p: T => Boolean): List[T] = this match {
        case Nil => Nil
        case Cons(y, ys) =>
          val r = ys.filter(p)
          if (p(y)) Cons(y, r) else r
      }

      def map[U](f: T => U): List[U] = this match {
        case Nil => Nil
        case Cons(y, ys) => Cons(f(y), ys.map(f))
      }

      def foldRight[B](z: B, f: (T, B) => B): B = this match {
        case Nil => z
        case Cons(h, t) => f(h, t.foldRight(z, f))
      }


    }


    case object Nil extends List[Nothing]

    case class Cons[T](x: T, xs: List[T]) extends List[T]


    /**
     * Streams.
     */
    sealed abstract class Stream[+T] {

      def head(): T = this match {
        case SNil => throw new RuntimeException("stream is empty")
        case SCons(x, _) => x()
      }

      def tail(): Stream[T] = this match {
        case SNil => throw new RuntimeException("stream is empty")
        case SCons(_, xs) => xs()
      }

      def map[U](f: T => U): Stream[U] = this match {
        case SNil => SNil
        case SCons(x, xs) => SCons(() => f(x()), () => xs().map(f))
      }

      def foreach(f: T => Unit): Unit = this match {
        case SNil =>
        case SCons(x, xs) =>
          f(x())
          xs().foreach(f)
      }

      def filter(p: T => Boolean): Stream[T] = this match {
        case SNil => SNil
        case SCons(x, xs) => if (p(x())) SCons(x, () => xs().filter(p)) else xs().filter(p)
      }

      def zip[U](ys: Stream[U]): Stream[(T, U)] = this match {
        case SNil => SNil
        case SCons(x, xs) => ys match {
          case SNil => SNil
          case SCons(z, zs) => SCons(() => (x(), z()), () => xs().zip(zs()))
        }
      }

      def take(n: Int): Stream[T] =
        if (n == 0) SNil else SCons(() => head(), () => tail().take(n - 1))

      def foldRight[B](z: () => B, f: (T, () => B) => B): B = this match {
        case SNil => z()
        case SCons(h, t) => f(h(), () => t().foldRight(z, f))
      }

      def toList(): List[T] = this match {
        case SNil => Nil
        case SCons(x, xs) => Cons(x(), xs().toList())
      }
    }

    case object SNil extends Stream[Nothing]

    case class SCons[T](x: () => T, xs: () => Stream[T]) extends Stream[T]


    val s1: Stream[Int] =
      SCons(() => 1, () =>
        SCons(() => 2, () =>
          SCons(() => 3, () =>
            SNil)))

    println(s"first element of s1: ${s1.head()}")
    println(s"second element of s1: ${s1.tail().head()}")

    def listToStream[T](xs: List[T]): Stream[T] = xs match {
      case Nil => SNil
      case Cons(y, ys) => SCons(() => y, () => listToStream(ys))
    }

    def unfoldRight[A, S](z: S, f: S => Option[(A, S)]): Stream[A] =
      f(z) match {
        case Some((h, s)) => SCons(() => h, () => unfoldRight(s, f))
        case None => SNil
      }

    val ones: Stream[Int] = {
      unfoldRight(1, (i: Int) => Some(i, i))
    }

    val nats: Stream[Int] = {
      unfoldRight(0, (i: Int) => Some(i, i+1))
    }

    val fibs: Stream[Int] = {
      unfoldRight((0, 1), (x: Int, y: Int) => Some(x, (x+y, x)))
    }

    println("Fibonacci:")
    fibs.take(25).foreach(println)

    def sieve(xs: Stream[Int]): Stream[Int] =
      SCons(() => xs.head(), () => sieve(xs.tail().filter(x => x % xs.head() != 0)))

    val primes = sieve(nats.tail().tail())

    println("Primes:")
    primes.take(100).foreach(println)

    def fibs2(): Stream[Int] =
      SCons(() => 0, () =>
        SCons(() => 1, () =>
          fibs2().zip(fibs2().tail()).map(n => n._1 + n._2)))

    println("Fibonacci again:")
    fibs2().take(25).foreach(println)

    println(s"Fibonacci as list: ${fibs2().take(25).toList()}")

    class Sighting(
                    val animal: String, // Which animal
                    val spotter: Int, // Who saw it
                    val count: Int, // How many
                    val area: Int, // Where
                    val period: Int // When
                  )

    val sightings: List[Sighting] =
      Cons(new Sighting("Elephant", 17, 5, 3, 1),
        Cons(new Sighting("Lion", 2, 5, 3, 2),
          Cons(new Sighting("Elephant", 2, 3, 3, 2),
            Nil)))

    val elephants1: Int =
      sightings.filter(s => s.animal == "Elephant")
        .map(s => s.count)
        .foldRight(0, (x: Int, res: Int) => x + res)
    println(s"Elephant sightings: $elephants1")

    val elephants2: Int =
      listToStream(sightings).filter(s => s.animal == "Elephant")
        .map(s => s.count)
        .foldRight(() => 0, (x: Int, res: () => Int) => x + res())
    println(s"Elephant sightings: $elephants2")

  }
}
