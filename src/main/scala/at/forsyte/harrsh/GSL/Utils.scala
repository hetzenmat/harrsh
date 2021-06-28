package at.forsyte.harrsh.GSL

import at.forsyte.harrsh.GSL.projections.prototype.StackForestProjection
import at.forsyte.harrsh.seplog.Var

import scala.collection.mutable.ArrayBuffer

object Utils {

  private def _debugRequire(cond: Boolean): Unit = _debugRequireMsg(cond, "")

  private def _debugRequireMsg(cond: Boolean, message: String): Unit = {
    if (!cond) {
      throw new IllegalStateException(message)
    }
  }

  var debugRequireMsg: (Boolean, String) => Unit = _debugRequireMsg
  var debugRequire: Boolean => Unit = _debugRequire

  def enableDebugRequire(): Unit = {
    debugRequireMsg = _debugRequireMsg
    debugRequire = _debugRequire
  }

  def disableDebugRequire(): Unit = {
    debugRequireMsg = (_, _) => ()
    debugRequire = _ => ()
  }

  implicit class SetUtils[A](val s: Set[A]) {
    def disjoint(other: Set[A]): Boolean = s.intersect(other).isEmpty
  }

  def isCanonical(t: Iterable[PhiType], ac: AliasingConstraint[Var]): Boolean =
    t.forall(t => isCanonicalSF(t.projections, ac))

  def isCanonical(t: PhiType, ac: AliasingConstraint[Var]): Boolean =
    isCanonicalSF(t.projections, ac)

  def isCanonicalSF(s: Iterable[StackForestProjection], ac: AliasingConstraint[Var]): Boolean =
    s.forall(sf => sf.freeVars.forall(v => ac.largestAlias(v) == v))

  def compareLexicographically[A](a: Seq[A], b: Seq[A])(implicit evidence: A => Ordered[A]): Int = {
    val res = a.zip(b).collectFirst({
      case (v1, v2) if v1 < v2 => -1
      case (v1, v2) if v1 > v2 => 1
    })
    res match {
      case None => a.size.compareTo(b.size)
      case Some(x) => x
    }
  }

  def chainIterators[A](elems: IterableOnce[Iterator[A]]): Iterator[A] = new Iterator[A] {
    val elemsIterator: Iterator[Iterator[A]] = elems.iterator
    var currentIterator: Iterator[A] = Iterator.empty
    searchNext()

    private def searchNext(): Unit = while (!currentIterator.hasNext && elemsIterator.hasNext) currentIterator = elemsIterator.next()

    override def hasNext: Boolean = currentIterator.hasNext

    override def next(): A = {
      val a = currentIterator.next()
      searchNext()

      a
    }
  }

  //  def chainIterators[A, B](sequence: IndexedSeq[A], f: A => Iterator[B]): Iterator[B] = new Iterator[B] {
  //    var currentIterator: Iterator[B] = Iterator.empty
  //    var index: Int = -1
  //    searchNext()
  //
  //    override def hasNext: Boolean = index <= sequence.size && currentIterator.hasNext
  //
  //    private def searchNext(): Unit = {
  //      while (!currentIterator.hasNext && index < sequence.size) {
  //        index += 1
  //        currentIterator = f(sequence(index))
  //      }
  //    }
  //
  //    override def next(): B = {
  //      val a = currentIterator.next()
  //      searchNext()
  //
  //      a
  //    }
  //  }

  def allAssignments[A, B](elems: Seq[A], values: Seq[B]): Seq[Seq[(A, B)]] = {
    require(values.nonEmpty)
    require(elems.nonEmpty)

    def aux(elems: Seq[A]): Seq[Seq[(A, B)]] = {
      elems match {
        case Seq(a) => values.map(v => Seq((a, v)))
        case head +: tail => values.flatMap(i => aux(tail).map(v => (head, i) +: v))
      }
    }

    aux(elems)
  }

  def allAssignmentsMonotone(length: Int, values: IndexedSeq[Int]): IndexedSeq[(Int, IndexedSeq[Int])] = {
    require(values.nonEmpty)

    val choices = ArrayBuffer.empty[(Int, IndexedSeq[Int])]
    var currentLength = 0
    while (currentLength < length) {
      val size = choices.length
      var i = 0
      while (i < size) {
        i += 1

        val (c, s) = choices(i)
        choices.update(i, (c + 1, -(c + 1) +: s))

        values.foreach { v => choices.addOne((c, v +: s)) }
      }

      currentLength += 1
    }

    //    def aux(length: Int): IndexedSeq[(Int, IndexedSeq[Int])] =
    //      length match {
    //        case 1 => (1, IndexedSeq(-1)) +: values.map(v => (0, IndexedSeq(v)))
    //        case _ => values.flatMap(v => aux(length - 1).flatMap({ case (c, value) =>
    //          Seq((c, -c +: value), (c + 1, -(c + 1) +: value), (c, v +: value))
    //        }))
    //      }

    choices.toIndexedSeq
  }

  def allAssignments[A](length: Int, values: IndexedSeq[A]): IndexedSeq[IndexedSeq[A]] = {
    require(values.nonEmpty)

    def aux(length: Int): IndexedSeq[IndexedSeq[A]] =
      length match {
        case 1 => values.map(v => IndexedSeq(v))
        case _ => values.flatMap(i => aux(length - 1).map(i +: _))
      }

    if (length == 0) IndexedSeq(IndexedSeq.empty)
    else aux(length)
  }

  def allSeqsWithRange(length: Int, range: Range): LazyList[Seq[Int]] = length match {
    case 1 => LazyList.from(range.map(i => Seq(i)))
    case _ => LazyList.from(range.flatMap(i => allSeqsWithRange(length - 1, range).map(i +: _)))
  }

  def isSortedStrict[A](a: IndexedSeq[A])(implicit evidence: Ordering[A]): Boolean = {
    var i = 0
    while (i + 1 < a.size) {
      if (evidence.gteq(a(i), a(i + 1))) return false

      i += 1
    }

    true
  }

  def isSorted[A](a: Seq[A])(implicit evidence: Ordering[A]): Boolean = {
    if (a.isEmpty)
      true
    else
      a.zip(a.tail).forall(t => evidence.lteq(t._1, t._2))
  }

  private def deleteHelper[A](v: IndexedSeq[A], n: Int): collection.mutable.Builder[A, IndexedSeq[A]] = {
    val b = v.iterableFactory.newBuilder[A]
    var i = 0
    v.foreach { x =>
      if (i != n) {
        b += x
      }
      i += 1
    }
    b
  }

  def insertInstead[A](v: IndexedSeq[A], n: Int, elems: IterableOnce[A]): IndexedSeq[A] = {
    val b = v.iterableFactory.newBuilder[A]
    var i = 0
    v.foreach { x =>
      if (i == n) b += x
      else b ++= elems

      i += 1
    }

    b.result()
  }

  @inline
  def deleteAt[A](v: IndexedSeq[A], n: Int): IndexedSeq[A] = {
    deleteHelper(v, n).result()
  }

  def deleteAtAndAppend[A](v: IndexedSeq[A], n: Int, elems: IterableOnce[A]): IndexedSeq[A] = {
    val b = deleteHelper(v, n)
    b.addAll(elems)

    b.result()
  }
}
