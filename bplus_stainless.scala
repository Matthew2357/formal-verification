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
  // LeafNode-specific code
  def search(key: BigInt) : Option[V] = {
    require(isOrdered(keys))
    keys.indexWhere(_==key)  match {
          case -1 => None[V]()
          case idx => Some(values(idx))
  }
}
}
