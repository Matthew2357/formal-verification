import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object BPlusTreeVerification {
  val MIN_ORDER: BigInt = 3

  // Core invariants
  sealed abstract class Tree {
    @extern
    def content: Set[BigInt] = {
      this match {
        case Leaf(keys, _) => keys.toSet
        case Internal(keys, children) => children.foldLeft(keys.toSet)((acc, c) => acc ++ c.content)
      }
    }

    def size: BigInt = this match {
      case Leaf(keys, _) => keys.size
      case Internal(_, children) => 1 + children.map(_.size).foldLeft(BigInt(0))(_ + _)
    }
  }

  case class Leaf(keys: List[BigInt], values: List[BigInt]) extends Tree
  case class Internal(keys: List[BigInt], children: List[Tree]) extends Tree

  // Basic validity checks
  def isValidTree(t: Tree, order: BigInt, isRoot: Boolean): Boolean = {
    require(order >= MIN_ORDER)
    t match {
      case Leaf(keys, values) => 
        keys.size == values.size &&
        isValidSize(keys.size, order, isRoot) &&
        isSorted(keys)
      case Internal(keys, children) =>
        keys.nonEmpty &&
        children.size == keys.size + 1 &&
        isValidSize(keys.size, order, isRoot) &&
        isSorted(keys) &&
        children.forall(c => isValidTree(c, order, false))
    }
  }

  def isValidSize(size: BigInt, order: BigInt, isRoot: Boolean): Boolean = {
    if (isRoot) size <= order
    else size >= (order + 1) / 2 && size <= order
  }

  def isSorted(keys: List[BigInt]): Boolean = {
    decreases(keys)
    keys match {
      case Nil() => true
      case Cons(_, Nil()) => true
      case Cons(x, l @ Cons(y, _)) => x < y && isSorted(l)
    }
  }

  @opaque
  def maxOfList(xs: List[BigInt]): BigInt = {
    require(xs.nonEmpty)
    decreases(xs)
    xs match {
      case Cons(h, Nil()) => h
      case Cons(h, t) =>
        val mt = maxOfList(t)
        if (h > mt) h else mt
    }
  }

  def treeHeight(t: Tree): BigInt = {
    t match {
      case Leaf(_, _) => 1
      case Internal(_, children) =>
        1 + (if (children.isEmpty) BigInt(0) else maxOfList(children.map(treeHeight)))
    }
  }

  // Core insert operation
  def insert(tree: Tree, key: BigInt, value: BigInt, order: BigInt, isRoot: Boolean): Tree = {
    require(
      order >= MIN_ORDER &&
      isValidTree(tree, order, isRoot) &&
      !contains(tree, key)
    )
    decreases(treeHeight(tree))

    tree match {
      case leaf @ Leaf(keys, values) =>
        if (keys.size < order) {
          insertIntoLeaf(leaf, key, value)
        } else {
          splitLeaf(leaf, key, value, order)
        }
      
      case internal @ Internal(keys, children) =>
        val pos = findPosition(keys, key)
        val newChild = insert(children(pos), key, value, order, false)
        balanceInternal(internal, newChild, pos, order)
    }
  }

  // Helper functions
  private def contains(tree: Tree, key: BigInt): Boolean = {
    decreases(treeHeight(tree))
    tree match {
      case Leaf(keys, _) => keys.contains(key)
      case Internal(keys, children) =>
        val pos = findPosition(keys, key)
        if (pos < keys.size && keys(pos) == key) true
        else contains(children(pos), key)
    }
  }

  private def findPosition(keys: List[BigInt], key: BigInt): BigInt = {
    require(isSorted(keys))
    decreases(keys)
    keys match {
      case Nil() => BigInt(0)
      case Cons(h, t) => 
        if (key < h) BigInt(0)
        else BigInt(1) + findPosition(t, key)
    }
  }.ensuring(res => res >= 0 && res <= keys.size)

  // Insert operations with minimal specs
  private def insertIntoLeaf(leaf: Leaf, key: BigInt, value: BigInt): Tree = {
    require(
      isSorted(leaf.keys) &&
      !leaf.keys.contains(key)
    )
    val pos = findPosition(leaf.keys, key)
    Leaf(
      leaf.keys.take(pos) ++ List(key) ++ leaf.keys.drop(pos),
      leaf.values.take(pos) ++ List(value) ++ leaf.values.drop(pos)
    )
  }

  // Split operations
  private def splitLeaf(leaf: Leaf, key: BigInt, value: BigInt, order: BigInt): Tree = {
    require(
      order >= MIN_ORDER &&
      isSorted(leaf.keys) &&
      !leaf.keys.contains(key) &&
      leaf.keys.size == order &&
      leaf.keys.size == leaf.values.size
    )
    
    val pos = findPosition(leaf.keys, key)
    val newKeys = insertIntoSorted(leaf.keys, key)
    val mid = order / 2

    assert(mid >= 0 && mid < newKeys.size)
    splitInvariants(newKeys, mid)

    Internal(
      List(newKeys(mid)),
      List(
        Leaf(newKeys.take(mid), leaf.values.take(mid)),
        Leaf(newKeys.drop(mid + 1), leaf.values.drop(mid))
      )
    )
  }

  private def balanceInternal(node: Internal, newChild: Tree, pos: BigInt, order: BigInt): Tree = {
    require(
      order >= MIN_ORDER &&
      isValidTree(node, order, false) &&
      isValidTree(newChild, order, false) &&
      pos >= 0 && pos < node.children.size
    )

    newChild match {
      case Internal(splitKeys, splitChildren) if splitKeys.size == 1 =>
        if (node.keys.size < order - 1) {
          // Simple merge
          Internal(
            node.keys.take(pos) ++ splitKeys ++ node.keys.drop(pos),
            node.children.take(pos) ++ splitChildren ++ node.children.drop(pos + 1)
          )
        } else {
          // Need to split internal node
          val allKeys = node.keys.take(pos) ++ splitKeys ++ node.keys.drop(pos)
          val allChildren = node.children.take(pos) ++ splitChildren ++ node.children.drop(pos + 1)
          val mid = order / 2
          
          Internal(
            List(allKeys(mid)),
            List(
              Internal(allKeys.take(mid), allChildren.take(mid + 1)),
              Internal(allKeys.drop(mid + 1), allChildren.drop(mid + 1))
            )
          )
        }
      case _ =>
        Internal(node.keys, node.children.updated(pos, newChild))
    }
  }

  // Helper functions for list operations
  private def insertIntoSorted(keys: List[BigInt], key: BigInt): List[BigInt] = {
    require(isSorted(keys) && !keys.contains(key))
    decreases(keys)
    keys match {
      case Nil() => List(key)
      case Cons(h, t) => 
        if (key < h) key :: keys
        else h :: insertIntoSorted(t, key)
    }
  }.ensuring(res => 
    isSorted(res) && 
    res.contains(key) &&
    res.size == keys.size + 1
  )

  // Verification lemmas
  @opaque
  def insertOrderPreservation(keys: List[BigInt], key: BigInt): Boolean = {
    require(isSorted(keys) && !keys.contains(key))
    decreases(keys)
    keys match {
      case Nil() => true
      case Cons(h, t) =>
        if (key < h) {
          BPlusTreeSpecs.orderedSpread(Nil(), key, keys)
          true
        } else {
          insertOrderPreservation(t, key) &&
          BPlusTreeSpecs.orderedSpread(List(h), key, t)
          true
        }
    }
  }.ensuring(_ => isSorted(insertIntoSorted(keys, key)))

  @opaque
  def splitPreservation(keys: List[BigInt], at: BigInt): Boolean = {
    require(isSorted(keys) && at >= 0 && at < keys.size)
    decreases(keys)
    
    val (left, right) = (keys.take(at), keys.drop(at))
    isSorted(left) && isSorted(right) &&
    left.forall(k => right.forall(k < _))
  }.ensuring(_ == true)

  @opaque
  def mergePreservation(l1: List[BigInt], l2: List[BigInt]): Boolean = {
    require(
      isSorted(l1) && isSorted(l2) &&
      l1.forall(k1 => l2.forall(k2 => k1 < k2))
    )
    decreases(l1)
    l1 match {
      case Nil() => true
      case Cons(h, t) => mergePreservation(t, l2)
    }
  }.ensuring(_ => isSorted(l1 ++ l2))

  def listInvariants(keys: List[BigInt]): Boolean = {
    keys.size >= 0 && isSorted(keys)
  }

  def splitInvariants(keys: List[BigInt], at: BigInt): Boolean = {
    require(at >= 0 && at < keys.size && listInvariants(keys))
    val left = keys.take(at)
    val right = keys.drop(at)
    listInvariants(left) && listInvariants(right) &&
    left.size == at &&
    right.size == keys.size - at &&
    (left.isEmpty || right.isEmpty || left.last < right.head)
  }

  // Add helper for key distribution
  @opaque
  def keyDistributionLemma(keys: List[BigInt], at: BigInt, key: BigInt): Boolean = {
    require(
      isSorted(keys) && 
      !keys.contains(key) &&
      at >= 0 && at < keys.size
    )
    decreases(keys)
    
    val newKeys = insertIntoSorted(keys, key)
    val (left, right) = (newKeys.take(at), newKeys.drop(at))
    
    BPlusTreeSpecs.orderedSpread(left, newKeys(at), right)
  }.ensuring(_ == true)
}

// Helper specs object similar to RedBlackTreeSpecs
object BPlusTreeSpecs {
  import BPlusTreeVerification._ // Import definitions from main object

  def orderedSpread(l1: List[BigInt], x: BigInt, l2: List[BigInt]): Boolean = {
    require(isSorted(l1) && isSorted(l2))
    l1.forall(_ < x) && l2.forall(x < _)
  }.ensuring(_ ==> 
    isSorted(l1 ++ List(x) ++ l2)
  )

  def insertPreservesOrder(list: List[BigInt], x: BigInt): Boolean = {
    require(isSorted(list) && !list.contains(x))
    decreases(list)
    list match {
      case Nil() => true
      case Cons(h, t) => 
        if (x < h) orderedSpread(Nil(), x, list)
        else insertPreservesOrder(t, x) && h < x
    }
  }.ensuring(_ == true)
}
