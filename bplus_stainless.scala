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

case class LeafNode[V](keys: List[BigInt], values: List[V], override val order: BigInt, next: Option[LeafNode[V]]) extends Node[V] {

  //make sure that conditions we need are met
  def isGood(): Boolean =  {
    isOrdered(keys) && keys.length == values.length && keys.length <= order && !keys.isEmpty
  }


  def search(key: BigInt): Option[V] = {
    //require(isOrdered(keys) && keys.length == values.length) // Ensure keys and values align
    require(this.isGood())
    keys match {
      case Nil() => None[V]()
      case _ =>
        val idx = keys.indexWhere(_ == key)
        if (idx >= 0 && idx < values.length) Some[V](values(idx))
        else None[V]()
    }
  }

  //how many keys in the leaf?
  def size(): BigInt ={
    require(this.isGood())
    keys.length
  }.ensuring(res => res <= order) 

  //insert without split
  def insertNoSplit(key: BigInt, value: V) : LeafNode[V] = {
    require(this.isGood() && keys.length < order)
    def getNewLists(key: BigInt, value: V, keys: List[BigInt], values : List[V], ord : BigInt) : (List[BigInt], List[V]) = {
      require(values.length == keys.length && keys.length < ord && isOrdered(keys))
      keys match {
        case Nil() => (List(key), List(value))
        case Cons(head, tail) => 
          if(key <= head){
            val newkeys = Cons(key, keys)
            (newkeys, Cons(value, values))
          }else{
            val kv = getNewLists(key, value, tail, values.tail, ord-1)
            (Cons(head, kv._1), Cons(values.head, kv._2))
          }
      }
    }.ensuring(res => res._1.length == res._2.length && res._1.length <= ord && isOrdered(res._1))
    val newlists = getNewLists(key, value, keys, values, order)
    LeafNode[V](newlists._1, newlists._2, order, next)
  }.ensuring(res => res.isGood())
}

//insert with split
//roadmap: separate the node, and then insert the new key where it's supposed to go

object Tests{
  val keys = List[BigInt](1, 2, 3, 4, 6)
  val values = List("one", "two", "three", "four", "six")
  val testLeaf = LeafNode[String](keys, values, 10, None[LeafNode[String]]())
  val order1 = List[BigInt](1,3,5,7,10)
  val order2 = List[BigInt](4,1,2,6,10,9)
  val order3 = List[BigInt](5,5,5,5,5,5,5,6)
  val insert1 = List[BigInt](1,3,5,6,7,10)

  def searchTest(idx : BigInt, value: String): Boolean = {
      testLeaf.search(idx) match {
      case Some[String](foundValue) => foundValue == value // Compare the inner value
      case None[String]()        => false           // Handle the case where the Option is empty
    }
  }

  def searchTests(): Unit = {
    assert(searchTest(4, "four"))
    assert(!searchTest(4, "three"))
    assert(!searchTest(7, "xxxxx"))
  }

  def orderTests(): Unit = {
    assert(isOrdered(order1))
    assert(!isOrdered(order2))
    assert(isOrdered(order3))
  }

  def insertNoSplitTests(): Unit = {
    assert(testLeaf.insertNoSplit(5, "five") ==  LeafNode[String](List[BigInt](1, 2, 3, 4, 5, 6), List("one", "two", "three", "four", "five", "six"), 10, None[LeafNode[String]]()))
  }
}
