package slex.heapautomata

import slex.seplog.{PtrExpr, PureAtom}

/**
  * Created by jkatelaa on 10/17/16.
  */
class Closure(pure : Set[PureAtom]) {

  // FIXME: This closure class is ridiculously inefficient, having one copy of each equivalence class per member
  var mapToClasses : Map[FV,Set[FV]] = Map()

  // TODO Is this the right way now that we have switched to ordinary atoms?
  for {
    atom <- pure
    (left, right, isEqual) = unwrapAtom(atom)
    if isEqual
  } {
    extendEntry(left, right)
    //      println("Inserting " + left + " -> " + right)
    //      for {
    //        (key, vals) <- mapToClasses
    //      } println(key + " --> " + vals)
  }

  def getEqualityClass(fv : FV) : Set[FV] = mapToClasses.getOrElse(fv, Set(fv))

  def isMinimumInItsClass(fv : FV) : Boolean = {
    // If the EQ class is defined, check if i is the representation = the minimum of that class
    // Otherwise, no equality for i has been set, so i is the unique and hence minimal element, so it is the representation
    if (mapToClasses.isDefinedAt(fv)) {
      mapToClasses(fv).min(Ordering.fromLessThan[PtrExpr]({
        case p  => p._1 < p._2
      })) == fv
    } else {
      true
    }
  }

  private def extendEntry(key : FV, newVal : FV) = {
    val eqClass = if (mapToClasses.isDefinedAt(key)) {
      // Class is already defined, just add the new value
      mapToClasses(key) + newVal
    } else {
      // Key not in any known eq class yet
      // Either have to extend class for val, if known already, or create new class
      if (mapToClasses.isDefinedAt(newVal)) mapToClasses(newVal) + key else Set(key, newVal)
    }

    // Extend entry for all members of the eq class
    for {
      classMember <- eqClass
    } {
      mapToClasses = mapToClasses + (classMember -> eqClass)
    }
  }

}