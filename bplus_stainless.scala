import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

def isOrdered(list: List[BigInt]): Boolean = {
   
  list match {
    case Nil() => true  // Empty list or single-element list is always ordered
    case Cons(head, tail) =>
        tail match {
            case Nil() => true
            case h :: _ => // Ensure the condition properly returns a Boolean
            (head <= h) && isOrdered(tail)

        }
    
  }
}

sealed abstract class BPlusTree[V] {
  val order: BigInt
}

sealed abstract class Node[V] extends BPlusTree[V] 

case class InternalNode[V](keys: List[BigInt], children: List[Node[V]],  override val order: BigInt) extends Node[V] {
  // InternalNode-specific code
}

case class LeafNode[V](keys: List[BigInt], values: List[V], override val order: BigInt) extends Node[V] {
  def search(key: BigInt): Option[V] = {
    require(isOrdered(keys) && keys.length == values.length) // Ensure keys and values align
    keys match {
      case Nil() => None[V]()
      case _ =>
        val idx = keys.indexWhere(_ == key)
        if (idx >= 0 && idx < values.length) Some[V](values(idx))
        else None[V]()
    }
  }
}

