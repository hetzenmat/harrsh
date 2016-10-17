package slex.heapautomata

import slex.Combinators
import slex.seplog.SymbolicHeap

/**
  * Created by jens on 10/15/16.
  */
trait HeapAutomaton {

  type State

  val description : String = "HA"

  val states : Set[State]

  def isFinal(s : State) :  Boolean

  /**
    * Is the given SH in the alphabet of this HA?
    */
  def isDefinedOn(lab : SymbolicHeap) : Boolean

  /**
    * Evaluates the transition function on the given src, trg, and SH; only meant for evaluating single transitions;
    * to iterate over defined transitions for a fixed SH, use getDefinedTransitions
    */
  def isTransitionDefined(src : Seq[State], trg : State, lab : SymbolicHeap) : Boolean

  /**
    * Returns all the state sequences on which transitions are defined for the given SH.
    * By default, this is implemented naively in terms of isTransitionDefined. Override if more efficient implementation exists for your SH>
    * @param lab
    * @return
    */
  def getDefinedTransitions(lab : SymbolicHeap) : Set[(Seq[State], State)] = {
    val sizeOfSig = lab.spatial.length
    val srcSeqs : Set[Seq[State]] = Combinators.allSeqsOfLength(sizeOfSig, states)

    for {
      src <- srcSeqs
      trg <- states
      if isTransitionDefined(src, trg, lab)
    } yield (src, trg)
  }

}