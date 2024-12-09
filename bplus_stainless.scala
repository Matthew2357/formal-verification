import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._

def isOrdered[K: Ordering](list: List[K]): Boolean = {
   // Get the Ordering for K
  list match {
    case Nil() => true  // Empty list or single-element list is always ordered
    case head :: tail =>
        tail match {
            case Nil() => true
            case h :: _ => // Ensure the condition properly returns a Boolean
            implicitly[Ordering[K]].lt(head, h) && isOrdered(tail)

        }
    
  }
}

sealed abstract class BPlusTree[K,V] {
  val order: BigInt
}

sealed abstract class Node[K,V] extends BPlusTree[K,V] 

case class InternalNode[K, V](keys: List[K], children: List[Node[K,V]], override val order: BigInt) extends Node[K, V] {
  // InternalNode-specific code
}

case class LeafNode[K: Ordering, V](keys: List[K], values: List[V], next: Option[Node[K, V]], override val order: BigInt) extends Node[K, V] {
  // LeafNode-specific code
  def search(key: K) : Option[V] = {
    require(isOrdered(keys))
    keys.indexWhere(_==key) match {
          case -1 => None.asInstanceOf[Option[V]]
          case idx => Some(values(idx))
  }
}
}
