import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._
import stainless.lang.Map.ToMapOps
import stainless.collection.ListSpecs._

object bplus_stainless {

  //strict order (no duplicates)
  def isOrdered(list: List[BigInt]): Boolean = {
    list match {
      case Nil() => true  // Empty list or single-element list is always ordered
      case Cons(head, tail) =>
          tail match {
              case Nil() => true
              case Cons(h,_) => // Ensure the condition properly returns a Boolean
              (head < h) && isOrdered(tail)
          }
    }
  }

  //statement: given an ordered list (strictly ordered, no duplicates) and a key such that the key is smaller
  //than the head of the list, then the key is not contained in the list
  def noSmallerKeysContained(list: List[BigInt], key: BigInt) : Unit = {
    require(!list.isEmpty && isOrdered(list) && key < list.head)
    list match {
      case Nil() => ()
      case Cons(head, tail) =>
      if(tail.isEmpty){
        ()
      }else{
        noSmallerKeysContained(tail, key)
      }
    }
  }.ensuring(!list.contains(key))

  //statement: if an ordered list is the concatenation of two lists, then those lists are also ordered
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

  //written by chatGPT
  def initAndLast(list: List[BigInt]): Unit = {
    require(!list.isEmpty)
    list match {
      case Cons(_, Nil()) => 
        ()
      case Cons(h, t) => 
        initAndLast(t)
    }
  }.ensuring(_ => list == list.init ++ List(list.last))

  //for when we split leaves: we want the last key in the first leaf to be smaller than the first in the second
  def biggestSmallest(l1: List[BigInt], l2: List[BigInt]) : Unit = {
    require(isOrdered(l1++l2))
    if(l1.isEmpty){()}else{
    initAndLast(l1)
    appendAssoc(l1.init, List(l1.last), l2)
    sublistsAreOrdered(l1.init, List(l1.last)++l2)
    }
  }.ensuring(_ => (!l1.isEmpty && !l2.isEmpty) ==> l1.last < l2.head)

  //written by chatGPT
  def mapConcatProperty[A, B](l1: List[(A, B)], l2: List[(A, B)]): Unit = {
    decreases(l1)
    (l1, l2) match {
      case (Nil(), _) => ()
      case (Cons(h1, t1), _) => mapConcatProperty(t1, l2)
    }
  }.ensuring(_ => 
    l1.map(_._1) ++ l2.map(_._1) == (l1 ++ l2).map(_._1)
  )

  //==========================End of helper functions================================================

  sealed abstract class BPlusTree[V] {
    val order: BigInt
  }

  sealed abstract class Node[V] extends BPlusTree[V] 

case class InternalNode[V](keys: List[BigInt], children: List[Node[V]], override val order: BigInt) extends Node[V] {

  def isGood(): Boolean = {
    keys.length + 1 == children.length &&
    keys.length <= order - 1 &&
    keys.length >= (order / 2) &&
    order >= 2 &&
    isOrdered(keys)
  }

  // Helper function to insert key into keys list
  def getNewKeys(key: BigInt, ks: List[BigInt], ord: BigInt): List[BigInt] = {
    require(ks.length < ord && isOrdered(ks) && !ks.contains(key))
    ks match {
      case Nil() => List(key)
      case Cons(h, t) =>
        if (key < h) {
          Cons(key, ks)
        } else {
          val newKs = getNewKeys(key, t, ord - 1)
          Cons(h, newKs)
        }
    }
  }.ensuring { res =>
    res.length <= ord &&
    res.length == ks.length + 1 &&
    isOrdered(res) &&
    (!ks.isEmpty ==> (res.head == (if (key < ks.head) key else ks.head))) &&
    (res.contains(key)) &&
    (ks.forall(k => res.contains(k)))
  }

  // Helper function to insert rightChild after leftChild in children list
  def getNewChildren(leftChild: Node[V], rightChild: Node[V], cs: List[Node[V]]): List[Node[V]] = {
    require(cs.contains(leftChild))
    cs match {
      case Cons(c, t) =>
        if (c == leftChild) {
          Cons(c, Cons(rightChild, t))
        } else {
          val newCs = getNewChildren(leftChild, rightChild, t)
          Cons(c, newCs)
        }
      case _ => cs // This case won't occur due to the require condition
    }
  }.ensuring { res =>
    res.length == cs.length + 1 &&
    res.contains(leftChild) &&
    res.contains(rightChild) &&
    cs.forall(child => res.contains(child) || child == leftChild)
  }

  // Insert into an internal node without splitting
  def insertNoSplit(key: BigInt, leftChild: Node[V], rightChild: Node[V]): InternalNode[V] = {
    require(this.isGood() && keys.length < order - 1 && children.contains(leftChild) && !keys.contains(key))
    val newKeys = getNewKeys(key, keys, order - 1)
    val newChildren = getNewChildren(leftChild, rightChild, children)
    InternalNode[V](newKeys, newChildren, order)
  }.ensuring { res =>
    res.isGood() &&
    res.keys.length == this.keys.length + 1 &&
    res.children.length == this.children.length + 1 &&
    res.children.contains(rightChild)
  }

  // Insert into an internal node with splitting
  def insertSplit(key: BigInt, leftChild: Node[V], rightChild: Node[V]): (InternalNode[V], InternalNode[V], BigInt) = {
    require(this.isGood() && keys.length == order - 1 && children.contains(leftChild) && !keys.contains(key))
    val newKeys = getNewKeys(key, keys, order)
    val newChildren = getNewChildren(leftChild, rightChild, children)
    val mid = newKeys.length / 2
    val promotedKey = newKeys(mid)
    val leftKeys = newKeys.take(mid)
    val rightKeys = newKeys.drop(mid + 1)
    val leftChildren = newChildren.take(mid + 1)
    val rightChildren = newChildren.drop(mid + 1)
    val leftNode = InternalNode[V](leftKeys, leftChildren, order)
    val rightNode = InternalNode[V](rightKeys, rightChildren, order)
    (leftNode, rightNode, promotedKey)
  }.ensuring { res =>
    val (leftNode, rightNode, promotedKey) = res
    leftNode.isGood() &&
    rightNode.isGood() &&
    leftNode.keys.length >= (order / 2) &&
    rightNode.keys.length >= (order / 2) &&
    isOrdered(leftNode.keys ++ (promotedKey :: rightNode.keys)) &&
    leftNode.keys.lastOption.getOrElse(BigInt(0)) < promotedKey &&
    promotedKey < rightNode.keys.headOption.getOrElse(BigInt(0))
  }

  // Insert into internal node
  def insertInternal(key: BigInt, leftChild: Node[V], rightChild: Node[V]): Either[InternalNode[V], (InternalNode[V], InternalNode[V], BigInt)] = {
    require(this.isGood() && children.contains(leftChild) && !keys.contains(key))
    if (keys.length < order - 1) {
      val newNode = insertNoSplit(key, leftChild, rightChild)
      Left(newNode)
    } else {
      val splitResult = insertSplit(key, leftChild, rightChild)
      Right(splitResult)
    }
  }.ensuring { res =>
    res match {
      case Left(node) => node.isGood()
      case Right((leftNode, rightNode, promotedKey)) =>
        leftNode.isGood() && rightNode.isGood() &&
        leftNode.keys.lastOption.getOrElse(BigInt(0)) < promotedKey &&
        promotedKey < rightNode.keys.headOption.getOrElse(BigInt(0))
    }
  }
}

  case class LeafNode[V](val keyValues : List[(BigInt, V)], override val order: BigInt, val next: Option[LeafNode[V]]) extends Node[V] {
    
    //make sure that conditions we need are met
    def isGood(): Boolean =  {
      isOrdered(keyValues.map(_._1)) && this.size() <= order && 2*this.size() >= order && order >= 2
    }

    def isAlmostGood(): Boolean = {
      isOrdered(keyValues.map(_._1)) && this.size() <= order && this.size() >= order/2 && order >= 2
    }

    def search(key: BigInt): Option[V] = {
      require(this.isGood())
      keyValues match {
        case Nil() => None[V]()
        case _ =>
          val idx = keyValues.map(_._1).indexWhere(_ == key)
          if (idx >= 0 && idx < keyValues.length && keyValues.map(_._1).contains(key)) { //kinda redundant, but it doesn't hurt
            Some[V](keyValues(idx)._2)
          }else{ 
            None[V]()
          }
      }
    }.ensuring(res => res != None[V]() ==> this.keyValues.map(_._1).contains(key))

    //how many keys in the leaf?
    def size(): BigInt ={
      keyValues.length
    }
    
    //helper function for insertion
    def getNewList(key: BigInt, value: V, kvs: List[(BigInt, V)], ord: BigInt) : List[(BigInt, V)] = {
      require(kvs.length < ord && isOrdered(kvs.map(_._1)) && !kvs.map(_._1).contains(key))
      kvs match {
        case Nil() => List((key, value))
        case Cons(head, tail) => 
          if(key < head._1){
            Cons((key, value), kvs)
          }else{
            val kv = getNewList(key, value, tail, ord-1)
            Cons(head, kv)
          }
      }
    }.ensuring(res => res.length <= ord && res.length == kvs.length+1 && isOrdered(res.map(_._1)))

    //insert in a leaf that is not full
    def insertNoSplit(key: BigInt, value: V) : LeafNode[V] = {
      require(this.isGood() && this.size() < order && !keyValues.map(_._1).contains(key))
      val newlist = getNewList(key, value, keyValues, order)
      LeafNode[V](newlist, order, next)
    }.ensuring(res => res.isGood() && res.size() == this.size()+1)

    //insert with split
    def insertSplit(key: BigInt, value: V) : (LeafNode[V], LeafNode[V]) = {
      require(this.isGood() && this.size() == order && !keyValues.map(_._1).contains(key))
      val newlist = getNewList(key, value, keyValues, order+1)

      //helper function that takes a list of length order+1 and splits it into two
      //we could do without introducing steps, it is redundant
      //it just makes my thinking a bit easier
      //the intuition is to start with one list and one empty one, and transfer an element from one list to the other until we have two lists of the desired lengths
      def splitList(l1: List[(BigInt, V)], l2: List[(BigInt, V)], n: BigInt, steps: BigInt, m: BigInt) : (List[(BigInt, V)], List[(BigInt, V)]) = {
        //n -> total number of elements, m -> number we want to move from l2 to l1, steps -> number of steps left
        require(
        (l1++l2).length == n && 
        isOrdered(l1.map(_._1)++l2.map(_._1)) && 
        l1.length == m-steps && 
        l2.length == n-(m-steps) && 
        m <= n && 
        steps <= m && 
        m>0 && 
        n>0 && 
        steps>= 0
        ) 

        decreases(steps)
        if(steps==0){
          biggestSmallest(l1.map(_._1), l2.map(_._1))
          (l1, l2)
        }else{
          val h = l2.head
          val t = l2.tail
          appendAssoc(l1.map(_._1), List(h).map(_._1), t.map(_._1))
          mapConcatProperty[BigInt, V](l1,List(h))
          splitList(l1++List(h), t, n, steps-1, m)
        }

      }.ensuring(
      res => (res._1 ++ res._2).length == n && 
      isOrdered(res._1.map(_._1) ++ res._2.map(_._1)) && 
      res._1.length == m && res._2.length ==n-m && 
      m <= n && 
      steps <= m && 
      m>0 && 
      n>0 && 
      steps>= 0 &&
      (!res._1.isEmpty && !res._2.isEmpty) ==> res._1.map(_._1).last < res._2.map(_._1).head
      )

      val splitlist = splitList(Nil[(BigInt, V)](), newlist, order+1, (order/2)+1, (order/2)+1)
      sublistsAreOrdered(splitlist._1.map(_._1), splitlist._2.map(_._1))
      val lfnode2 = LeafNode[V](splitlist._2, order, this.next)
      val lfnode1 = LeafNode[V](splitlist._1, order, Some[LeafNode[V]](lfnode2))
      (lfnode1, lfnode2)
      //note: in scala rounding is always done towards zero, so (order+1)/2 is the same as ceil(order/2)
      }.ensuring(
      res => res._1.isGood() && 
      res._2.isGood() &&
      res._1.size()==(order/2)+1 && 
      res._2.size()==(order+1)/2 && 
      res._1.next == Some(res._2) && res._2.next == this.next &&
      res._1.keyValues.map(_._1).last < res._2.keyValues.map(_._1).head
      ) 
      
      def easyDelete(key: BigInt) : (LeafNode[V], Boolean) = {
        require(this.size() > (order+1)/2 && this.isGood())
        def deleteFromList(key: BigInt, l: List[(BigInt, V)]) : List[(BigInt, V)] = {
          require(isOrdered(l.map(_._1)) && l.map(_._1).contains(key))
          l match {
            case Cons(head, tail) =>
            if(head._1 == key){
              if(tail.isEmpty){tail}else{
              sublistsAreOrdered(List(head._1), tail.map(_._1))
              noSmallerKeysContained(tail.map(_._1), key)
              tail}
            }else{
              Cons(head, deleteFromList(key, tail))
            }
          }
        }.ensuring(res => res.length == l.length-1 && isOrdered(res.map(_._1)) && !res.map(_._1).contains(key))
        this.search(key) match {
          case None[V]() => (this, false)
          case _ =>
          (LeafNode[V](deleteFromList(key, this.keyValues), this.order, this.next), true)
        }
      }ensuring(
        res=>this.isGood() && 
        ((res._1.size() == this.size() && !res._2) || (res._1.size() == this.size() -1 && res._2))
        )
      
      //given a leaf node, we merge with the next one
      def MergeWithNext(): LeafNode[V] = {
      require(
        this.next.isDefined && 
        (this.size() + this.next.get.size() <= order) && 
        this.isAlmostGood() && this.next.get.isAlmostGood() &&
        this.keyValues.map(_._1).last < this.next.get.keyValues.map(_._1).head
      )
      this

}

      
  
    }

  //===============================What we have proven so far=============================================
  /*
  various lemmas:
  see the top of the file

  for leaf nodes:
  -if a search returns None, then the key is not contained in the keyValues list
  -insert in a leaf that is not full: the leaf remains ordered, and the size goes up by one
  -insert in a full leaf: the leaf splits, the left leaf has >=ceil(n/2) keys and the right one has ceil(n/2)
    also, the right leaf points to the next of the old leaf, and the left one points to the right
    finally, both new leaves respect all conditions (order etc) and the largest key of the left leaf is less than the smallest of the right leaf
  -when we delete from a leaf that has strictly more than ceil(n/2) elements (i.e. no need for merging), then the 
    leaf retains all properties, and its size goes down by one if the key was found, otherwise it does not change
  */

  //====================================================Tests (put this in a different file?)====================================


}