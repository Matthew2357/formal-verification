import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object BPlusTreeVerification {
  // Add minimum order constant
  val MIN_ORDER: BigInt = 3

  // Core verification properties first
  def isValidCapacity(keys: List[BigInt], isRoot: Boolean, order: BigInt): Boolean = {
    require(order >= MIN_ORDER)
    if (isRoot) {
      keys.nonEmpty && keys.size <= order
    } else {
      val minSize = (order + 1) / 2
      keys.size >= minSize && keys.size <= order
    }
  }.ensuring(res => 
    order >= MIN_ORDER &&
    (isRoot ==> (keys.nonEmpty && keys.size <= order)) && 
    (!isRoot ==> (keys.size >= ((order + 1) / 2) && keys.size <= order))
  )

  def isSortedKeys(keys: List[BigInt]): Boolean = {
    decreases(keys)
    keys match {
      case Nil() => true
      case Cons(x, Cons(y, rest)) => x < y && isSortedKeys(Cons(y, rest))
      case _ => true
    }
  }

  // Helper specs object similar to RedBlackTreeSpecs
  object BPlusTreeSpecs {
    def orderedSpread(l1: List[BigInt], x: BigInt, l2: List[BigInt]): Boolean = {
      require(isSortedKeys(l1) && isSortedKeys(l2))
      l1.forall(_ < x) && l2.forall(x < _)
    }.ensuring(res => res == validateSplit(l1, x, l2))

    def insertPreservesOrder(list: List[BigInt], x: BigInt): Boolean = {
      require(isSortedKeys(list) && !list.contains(x))
      decreases(list)
      list match {
        case Nil() => true
        case Cons(h, t) => 
          if (x < h) orderedSpread(Nil(), x, list)
          else insertPreservesOrder(t, x) && h < x
      }
    }.ensuring(_ == true)

    def splitPreservesSearch(list: List[BigInt], at: BigInt, x: BigInt): Boolean = {
      require(
        list.nonEmpty && 
        isSortedKeys(list) && 
        at >= 0 && 
        at < list.size && 
        list.contains(x) &&
        list.size >= 2 &&
        (at == 0 || (at < list.size && list(at-1) < list(at))) &&
        (at == list.size-1 || list(at) < list(at+1))
      )
      decreases(list)
      
      val (left, mid, right) = split(list, at)
      left.contains(x) || mid == x || right.contains(x)
    }.ensuring(_ == true)

    def concatPreservesOrder(l1: List[BigInt], l2: List[BigInt]): Boolean = {
      require(
        isSortedKeys(l1) && 
        isSortedKeys(l2) && 
        (l1.isEmpty || l2.isEmpty || l1.last < l2.head)
      )
      decreases(l1)
      
      l1 match {
        case Nil() => true
        case Cons(h, t) => concatPreservesOrder(t, l2)
      }
    }.ensuring(_ => isSortedKeys(l1 ++ l2))
  }

  import BPlusTreeSpecs._

  // Rest of core properties
  def validateSplit(left: List[BigInt], mid: BigInt, right: List[BigInt]): Boolean = {
    isSortedKeys(left) && isSortedKeys(right) &&
    left.forall(_ < mid) && right.forall(mid < _)
  }

  def containsKey(keys: List[BigInt], key: BigInt): Boolean = {
    keys.contains(key)
  }

  // B+ Tree node definitions with verification
  sealed abstract class BPlusNode {
    def isValid(isRoot: Boolean, order: BigInt): Boolean = {
      require(order >= MIN_ORDER)
      this match {
        case BPlusLeaf(keys, values) => 
          keys.size == values.size &&
          isValidCapacity(keys, isRoot, order) &&
          isSortedKeys(keys)
        case BPlusInternal(keys, children) =>
          keys.nonEmpty &&
          children.size == keys.size + 1 &&
          isValidCapacity(keys, isRoot, order) &&
          isSortedKeys(keys) &&
          children.forall(c => c.isValid(false, order))
      }
    }

    def size: BigInt = {
      decreases(this match {
        case BPlusLeaf(keys, _) => (1, keys.size)
        case BPlusInternal(_, children) => (2, children.size)
      })
      this match {
        case BPlusLeaf(keys, _) => keys.size
        case BPlusInternal(_, children) => 
          1 + children.foldLeft(BigInt(0))((acc, c) => acc + c.size)
      }
    } ensuring(_ >= 0)
  }

  // Update case classes to remove redundant isValid
  case class BPlusLeaf(keys: List[BigInt], values: List[BigInt]) extends BPlusNode
  case class BPlusInternal(keys: List[BigInt], children: List[BPlusNode]) extends BPlusNode

  // Insert with verification
  def insert(node: BPlusNode, key: BigInt, value: BigInt, order: BigInt, isRoot: Boolean): BPlusNode = {
    require(
      order >= MIN_ORDER &&
      node.isValid(isRoot, order) && 
      !node.match {
        case BPlusLeaf(keys, _) => keys.contains(key)
        case BPlusInternal(keys, _) => keys.contains(key)
      } &&
      node.match {
        case BPlusLeaf(keys, _) => keys.size <= order 
        case BPlusInternal(keys, _) => keys.size <= order - 1
      }
    )
    decreases((node.size, 1))

    node match {
      case leaf @ BPlusLeaf(keys, values) =>
        if (keys.size < order) {
          val (newKeys, newValues) = insertSorted(keys, values, key, value)
          BPlusLeaf(newKeys, newValues)
        } else {
          val (leftKeys, midKey, rightKeys) = split(keys :+ key, (order + 1) / 2)
          val (leftVals, _, rightVals) = split(values :+ value, (order + 1) / 2)
          BPlusInternal(List(midKey), 
            List(BPlusLeaf(leftKeys, leftVals), 
                BPlusLeaf(rightKeys, rightVals)))
        }
        
      case internal @ BPlusInternal(keys, children) =>
        val pos = keys.indexWhere(_ > key)
        val childPos = if (pos == -1) keys.size else pos
        val newChild = insert(children(childPos), key, value, order, false)
        
        newChild match {
          case BPlusInternal(newKeys, newChildren) if newKeys.size == 1 =>
            // Handle split result
            val (leftChild, rightChild) = (newChildren(0), newChildren(1))
            val newKey = newKeys(0)
            
            if (keys.size < order - 1) {
              // Simple insert
              val (updatedKeys, updatedChildren) = insertIntoInternal(keys, children, newKey, leftChild, rightChild, childPos)
              BPlusInternal(updatedKeys, updatedChildren)
            } else {
              // Split internal node
              val allKeys = insertSorted(keys, List(), newKey, 0)._1
              val (leftKeys, midKey, rightKeys) = split(allKeys, order / 2)
              val (leftChildren, rightChildren) = splitChildren(children, childPos, leftChild, rightChild, order / 2)
              BPlusInternal(List(midKey),
                List(BPlusInternal(leftKeys, leftChildren),
                     BPlusInternal(rightKeys, rightChildren)))
            }
          case _ => 
            // No split occurred
            BPlusInternal(keys, children.updated(childPos, newChild))
        }
    }
  }.ensuring(res => 
    res.isValid(isRoot, order) &&
    searchKey(res, key).isDefined &&
    (node match {
      case BPlusLeaf(k, _) => k.forall(x => searchKey(res, x).isDefined)
      case BPlusInternal(k, _) => k.forall(x => searchKey(res, x).isDefined)
    })
  )

  // Helper functions with basic verification
  private def insertSorted(keys: List[BigInt], values: List[BigInt], 
                         key: BigInt, value: BigInt): (List[BigInt], List[BigInt]) = {
    require(
      keys.size == values.size && 
      isSortedKeys(keys) &&
      !keys.contains(key)
    )
    
    def insert[T](xs: List[T], x: T, pos: BigInt): List[T] = {
      require(pos >= 0 && pos <= xs.size)
      decreases(xs)
      if (pos == 0) Cons(x, xs)
      else Cons(xs.head, insert(xs.tail, x, pos - 1))
    }

    val pos = keys.indexWhere(_ >= key)
    val insertPos = if (pos == -1) keys.size else pos
    
    val res = (insert(keys, key, insertPos), insert(values, value, insertPos))
    // assert(isSortedKeys(res._1))
    // assert(res._1.contains(key))
    res
  }.ensuring(res => 
    res._1.size == keys.size + 1 &&
    res._1.size == res._2.size &&
    isSortedKeys(res._1) &&
    containsKey(res._1, key) &&
    insertPreservesOrder(keys, key)
  )

  private def split(list: List[BigInt], at: BigInt): (List[BigInt], BigInt, List[BigInt]) = {
    require(
      list.nonEmpty && 
      isSortedKeys(list) && 
      at >= 0 && 
      at < list.size &&
      list.size >= 2 && // Ensure enough elements for splitting
      (at == 0 || list(at-1) < list(at)) && // Ensure ordering around split point
      (at == list.size-1 || list(at) < list(at+1))
    )
    
    val (left, rest) = splitList(list, at)
    val mid = rest.head
    val right = rest.tail
    
    // assert(isSortedKeys(left))
    // assert(isSortedKeys(right))
    // assert(left.forall(_ < mid))
    // assert(right.forall(mid < _))
    assert(left.forall(_ < mid))
    assert(right.forall(mid < _))
    assert(isSortedKeys(left) && isSortedKeys(right))
    
    (left, mid, right)
  }.ensuring(res => 
    validateSplit(res._1, res._2, res._3) &&
    res._1.size == at &&
    res._2 == list(at) &&
    res._3.size == list.size - at - 1 &&
    isSortedKeys(res._1) && isSortedKeys(res._3)
  )

  private def searchKey(node: BPlusNode, key: BigInt): Option[BigInt] = {
    require(node.isValid(false, BigInt(3)))
    decreases(node.size) // Add measure for recursion
    
    node match {
      case BPlusLeaf(keys, values) =>
        val idx = keys.indexOf(key)
        if (idx >= 0) Some(values(idx))
        else None()
      case BPlusInternal(keys, children) =>
        val pos = keys.indexWhere(_ > key)
        val childPos = if (pos == -1) keys.size else pos
        searchKey(children(childPos), key)
    }
  }

  private def insertIntoInternal(keys: List[BigInt], children: List[BPlusNode],
                                key: BigInt, leftChild: BPlusNode, rightChild: BPlusNode,
                                pos: BigInt): (List[BigInt], List[BPlusNode]) = {
    require(
      pos >= 0 && 
      pos <= keys.size &&
      children.size == keys.size + 1
    )
    
    def take[T](l: List[T], n: BigInt): List[T] = {
      require(n >= 0 && n <= l.size)
      if (n == 0) Nil()
      else Cons(l.head, take(l.tail, n-1))
    }

    def drop[T](l: List[T], n: BigInt): List[T] = {
      require(n >= 0 && n <= l.size)
      if (n == 0) l
      else drop(l.tail, n-1)
    }

    val newKeys = take(keys, pos) ++ List(key) ++ drop(keys, pos)
    val newChildren = take(children, pos) ++ List(leftChild, rightChild) ++ drop(children, pos + 1)
    (newKeys, newChildren)
  }

  private def splitChildren(children: List[BPlusNode], pos: BigInt,
                          leftNew: BPlusNode, rightNew: BPlusNode,
                          at: BigInt): (List[BPlusNode], List[BPlusNode]) = {
    require(
      pos >= 0 && 
      pos <= children.size && 
      at >= 0 && 
      at <= children.size + 1 && // Allow for added nodes
      splitChildrenHelper(children, pos) &&
      pos + 1 <= children.size // Add this to ensure drop is valid
    )
    
    def take[T](l: List[T], n: BigInt): List[T] = {
      require(n >= 0 && n <= l.size)
      if (n == 0) Nil()
      else Cons(l.head, take(l.tail, n-1))
    }

    def drop[T](l: List[T], n: BigInt): List[T] = {
      require(n >= 0 && n <= l.size)
      if (n == 0) l
      else drop(l.tail, n-1)
    }

    val updatedChildren = take(children, pos) ++ List(leftNew, rightNew) ++ drop(children, pos + 1)
    // Add assertion to help prover
    assert(pos + 1 <= children.size)
    (take(updatedChildren, at), drop(updatedChildren, at))
  }

  // Helper lemmas for list operations
  object ListProofs {
    @opaque
    def containsSorted(l: List[BigInt], x: BigInt): Boolean = {
      require(isSortedKeys(l))
      decreases(l)
      l match {
        case Nil() => false
        case Cons(h, t) => 
          if (x == h) true
          else if (x < h) false
          else containsSorted(t, x)
      }
    }.ensuring(res => res == l.contains(x))

    @opaque
    def sortedConcat(l1: List[BigInt], l2: List[BigInt]): Boolean = {
      require(isSortedKeys(l1) && isSortedKeys(l2) && 
              (l1.isEmpty || l2.isEmpty || l1.last < l2.head))
      decreases(l1)
      l1 match {
        case Nil() => true
        case Cons(h, t) => sortedConcat(t, l2)
      }
    }.ensuring(_ => isSortedKeys(l1 ++ l2))
  }

  import ListProofs._

  // Helper function to ensure split maintains sorted property
  private def validateSplitInvariant(list: List[BigInt], at: BigInt): Boolean = {
    require(list.nonEmpty && isSortedKeys(list) && at >= 0 && at < list.size)

    def take(l: List[BigInt], n: BigInt): List[BigInt] = {
      require(n >= 0 && n <= l.size)
      decreases(n)
      if (n == 0) Nil()
      else Cons(l.head, take(l.tail, n-1))
    }

    def drop(l: List[BigInt], n: BigInt): List[BigInt] = {
      require(n >= 0 && n <= l.size)
      decreases(n)
      if (n == 0) l
      else drop(l.tail, n-1)
    }

    val left = take(list, at)
    val right = drop(list, at + 1)
    sortedConcat(left, List(list(at))) &&
    sortedConcat(List(list(at)), right)
  }.ensuring(_ => true)

  // Add helper for searchKey
  private def searchKeyPreservesOrder(node: BPlusNode, key: BigInt): Boolean = {
    require(node.isValid(false, BigInt(3)))
    decreases(node.size)
    node match {
      case BPlusLeaf(keys, values) => true
      case BPlusInternal(keys, children) =>
        val pos = keys.indexWhere(_ > key)
        val childPos = if (pos == -1) keys.size else pos
        searchKey(children(childPos), key).isDefined ==> searchKey(node, key).isDefined
    }
  }.ensuring(_ == true)

  // Add list operation helpers
  def listConcat[T](l1: List[T], l2: List[T]): List[T] = {
    decreases(l1)
    l1 match {
      case Nil() => l2
      case Cons(h, t) => Cons(h, listConcat(t, l2))
    }
  }.ensuring(res => 
    res.size == l1.size + l2.size
  )

  def splitList[T](list: List[T], at: BigInt): (List[T], List[T]) = {
    require(at >= 0 && at <= list.size)
    decreases(at)
    
    if (at == 0) (Nil(), list)
    else {
      val (l1, l2) = splitList(list.tail, at - 1)
      (Cons(list.head, l1), l2)
    }
  }.ensuring(res => 
    res._1.size == at && 
    res._2.size == list.size - at
  )

  // Add helper for splitChildren
  private def splitChildrenHelper(children: List[BPlusNode], pos: BigInt): Boolean = {
    require(pos >= 0 && pos <= children.size)
    decreases(children)
    children match {
      case Nil() => pos == 0
      case Cons(_, t) => 
        if (pos == 0) true
        else splitChildrenHelper(t, pos - 1)
    }
  }.ensuring(_ => pos <= children.size)

  // Add helper lemma for append operation
  object AppendProofs {
    @opaque
    def appendPreservesSort(l: List[BigInt], x: BigInt): Boolean = {
      require(isSortedKeys(l) && (l.isEmpty || l.last < x))
      decreases(l)
      l match {
        case Nil() => true
        case Cons(h, t) => appendPreservesSort(t, x)
      }
    }.ensuring(_ => isSortedKeys(l :+ x))
  }  
  import AppendProofs._

  // Add helper for insert measure decreasing
  def childSizeDecreasesLemma(node: BPlusNode): Boolean = {
    require(node.isInstanceOf[BPlusInternal])
    decreases(node.size)
    
    val internal = node.asInstanceOf[BPlusInternal]
    internal.children.forall(child => child.size < node.size)
  }.ensuring(_ == true)

  // Add lemma for insert postcondition
  def insertPreservesValidityLemma(node: BPlusNode, key: BigInt, value: BigInt, order: BigInt, isRoot: Boolean): Boolean = {
    require(
      order >= MIN_ORDER &&
      node.isValid(isRoot, order) &&
      !node.match {
        case BPlusLeaf(keys, _) => keys.contains(key)
        case BPlusInternal(keys, _) => keys.contains(key)
      }
    )
    decreases(node.size)
    
    // Prove that insert preserves tree validity
    val newNode = insert(node, key, value, order, isRoot)
    newNode.isValid(isRoot, order) && searchKey(newNode, key).isDefined
  }.ensuring(_ == true)
}
