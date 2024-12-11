import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._
import stainless.lang.Map.ToMapOps
import stainless.collection.ListSpecs._


def isOrdered(list: List[BigInt]): Boolean = {
  list match {
    case Nil() => true  // Empty list or single-element list is always ordered
    case Cons(head, tail) =>
        tail match {
            case Nil() => true
            case Cons(h,_) => // Ensure the condition properly returns a Boolean
            (head <= h) && isOrdered(tail)

        }
  }
}


def sublistsAreOrdered(l1: List[BigInt], l2: List[BigInt]) : Unit = {
  require(isOrdered(l1++l2))
  def ltwoordered(l1: List[BigInt], l2: List[BigInt]) : Unit = {
    require(isOrdered(l1++l2))
    l1 match {
    case Nil() => ()
    case Cons(head, tail) => ltwoordered(tail, l2)
    }
  }.ensuring(_=>isOrdered(l2))

  def loneordered(l1: List[BigInt], l2: List[BigInt]) : Unit = {
    require(isOrdered(l1++l2))
    l1 match {
      case Nil() => ()
      case Cons(head, tail) =>
      tail match {
        case Nil() => ()
        case Cons(t1, t2) =>
        assert(head <= t1)
        loneordered(tail, l2)
      }
    }
  }.ensuring(_=>isOrdered(l1))

  loneordered(l1, l2)
  ltwoordered(l1, l2)
}.ensuring(_=>isOrdered(l1) && isOrdered(l2))

sealed abstract class BPlusTree[V] {
  val order: BigInt
}

sealed abstract class Node[V] extends BPlusTree[V] 

case class InternalNode[V](keys: List[BigInt], children: List[Node[V]],  override val order: BigInt) extends Node[V] {
  // InternalNode-specific code
}

case class LeafNode[V](val keyValues : List[(BigInt, V)], override val order: BigInt, val next: Option[LeafNode[V]]) extends Node[V] {
  
  //make sure that conditions we need are met
  def isGood(): Boolean =  {
    isOrdered(keyValues.map(_._1)) && keyValues.length <= order && 2*keyValues.length >= order && order >= 1
  }

  def mapConcatProperty[A, B](l1: List[(A, B)], l2: List[(A, B)]): Unit = {
  decreases(l1)
  (l1, l2) match {
    case (Nil(), _) => ()
    case (Cons(h1, t1), _) => mapConcatProperty(t1, l2)
  }
}.ensuring(_ => 
  l1.map(_._1) ++ l2.map(_._1) == (l1 ++ l2).map(_._1)
)



  def search(key: BigInt): Option[V] = {
    require(this.isGood())
    keyValues match {
      case Nil() => None[V]()
      case _ =>
        val idx = keyValues.map(_._1).indexWhere(_ == key)
        if (idx >= 0 && idx < keyValues.length) Some[V](keyValues(idx)._2)
        else None[V]()
    }
  }

  //how many keys in the leaf?
  def size(): BigInt ={
    require(this.isGood())
    keyValues.length
  }.ensuring(res => res <= order && 2*res >= order) 
  
  //helper function for insertion
  def getNewList(key: BigInt, value: V, kvs: List[(BigInt, V)], ord: BigInt) : List[(BigInt, V)] = {
    require(kvs.length < ord && isOrdered(kvs.map(_._1)))
    kvs match {
      case Nil() => List((key, value))
      case Cons(head, tail) => 
        if(key <= head._1){
          Cons((key, value), kvs)
        }else{
          val kv = getNewList(key, value, tail, ord-1)
          Cons(head, kv)
        }
    }
  }.ensuring(res => res.length <= ord && res.length == kvs.length+1 && isOrdered(res.map(_._1)))

  //insert in a leaf that is not full
  def insertNoSplit(key: BigInt, value: V) : LeafNode[V] = {
    require(this.isGood() && keyValues.length < order)
    val newlist = getNewList(key, value, keyValues, order)
    LeafNode[V](newlist, order, next)
  }.ensuring(res => res.isGood())

  //insert with split
  def insertSplit(key: BigInt, value: V) : (LeafNode[V], LeafNode[V]) = {
    require(this.isGood() && keyValues.length == order)
    val newlist = getNewList(key, value, keyValues, order+1)
    def splitList(l1: List[(BigInt, V)], l2: List[(BigInt, V)], n: BigInt, steps: BigInt, m: BigInt) : (List[(BigInt, V)], List[(BigInt, V)]) = {
      //n -> total number of elements, m -> number we want to move from l2 to l1, steps -> number of steps left
      require((l1++l2).length == n && isOrdered(l1.map(_._1)++l2.map(_._1)) && l1.length == m-steps && l2.length == n-(m-steps) && m <= n && steps <= m && m>0 && n>0 && steps>= 0) 
      decreases(steps)
      if(steps==0){
        (l1, l2)
      }else{
        val h = l2.head
        val t = l2.tail
        appendAssoc(l1.map(_._1), List(h).map(_._1), t.map(_._1))
        mapConcatProperty[BigInt, V](l1,List(h))
        splitList(l1++List(h), t, n, steps-1, m)
      }
    }.ensuring(res => (res._1 ++ res._2).length == n && isOrdered(res._1.map(_._1) ++ res._2.map(_._1)) && res._1.length == m && res._2.length ==n-m&& m <= n && steps <= m && m>0 && n>0 && steps>= 0)
    val splitlist = splitList(Nil[(BigInt, V)](), newlist, order+1, (order/2)+1, (order/2)+1)
    sublistsAreOrdered(splitlist._1.map(_._1), splitlist._2.map(_._1))
    val lfnode2 = LeafNode[V](splitlist._2, order, this.next)
    val lfnode1 = LeafNode[V](splitlist._1, order, Some[LeafNode[V]](lfnode2))
    (lfnode1, lfnode2)
    //note: in scala rounding is always done towards zero, so (order+1)/2 is the same as ceil(order/2)
    }.ensuring(res => res._1.isGood() && res._2.isGood() &&res._1.keyValues.length==(order/2)+1 && res._2.keyValues.length==(order+1)/2 && res._1.next == Some(res._2) && res._2.next == this.next) 
}



object Tests{
  val testLeaf = LeafNode[String](List[(BigInt, String)]((1, "one"), (2, "two"), (3, "three"), (4, "four"), (6, "six")), 10, None[LeafNode[String]]())
  val order1 = List[BigInt](1,3,5,7,10)
  val order2 = List[BigInt](4,1,2,6,10,9)
  val order3 = List[BigInt](5,5,5,5,5,5,5,6)
  val testInsertLeaf = LeafNode[String](List[(BigInt, String)]((1, "one"), (2, "two"), (3, "three"), (4, "four"), (6, "six"), (7, "seven")), 6, None[LeafNode[String]]())
  val testInsertLeaf2 = LeafNode[String](List[(BigInt, String)]((4, "four"), (5, "five"), (6, "six")), 6, None[LeafNode[String]]())
  val testInsertLeaf1 = LeafNode[String](List[(BigInt, String)]((1, "one"), (2, "two"), (3, "three"), (4, "four")), 6, Some[LeafNode[String]](testInsertLeaf2))


  def searchTest(idx : BigInt, value: String): Boolean = {
      testLeaf.search(idx) match {
      case Some[String](foundValue) => foundValue == value 
      case None[String]()        => false           
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
    assert(testLeaf.insertNoSplit(5, "five") ==  LeafNode[String](List[(BigInt, String)]((1, "one"), (2, "two"), (3, "three"), (4, "four"), (5, "five"), (6, "six")), 10, None[LeafNode[String]]()))
  }

  /*def insertSplitTests(): Unit = {
    assert(testInsertLeaf.insertSplit(5, "five")==(testInsertLeaf1, testInsertLeaf2))
  }*/
  //stainless can't handle this test - see how to do tests with the TAs
}
