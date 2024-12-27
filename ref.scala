sealed trait Node[K, V]
case class InternalNode[K, V](keys: Vector[K], children: Vector[Node[K, V]]) extends Node[K, V]
case class LeafNode[K, V](keys: Vector[K], values: Vector[V], next: Option[LeafNode[K, V]]) extends Node[K, V]

class BPlusTree[K: Ordering, V](val order: Int, val root: Node[K, V] = LeafNode[K, V](Vector.empty, Vector.empty, None)) {

  def search(key: K): Option[V] = {
    def searchNode(node: Node[K, V]): Option[V] = node match {
      case LeafNode(keys, values, _) =>
        keys.indexWhere(implicitly[Ordering[K]].equiv(_, key)) match {
          case -1 => None
          case idx => Some(values(idx))
        }
      case InternalNode(keys, children) =>
        val idx = keys.indexWhere(implicitly[Ordering[K]].gt(_, key)) match {
          case -1 => keys.size
          case i => i
        }
        searchNode(children(idx))
    }
    searchNode(root)
  }

  def insert(key: K, value: V): BPlusTree[K, V] = {
    def insertNode(node: Node[K, V]): (Node[K, V], Option[(K, Node[K, V])]) = node match {
      case LeafNode(keys, values, next) =>
        val (idx, newKeys, newValues) = 
          keys.indexWhere(implicitly[Ordering[K]].gt(_, key)) match {
            case -1 => 
              // Insert at the end
              (keys.size, keys :+ key, values :+ value)
            case i => 
              // Insert at the correct position i
              (i, keys.take(i) ++ (key +: keys.drop(i)), values.take(i) ++ (value +: values.drop(i)))
          }

        // Split the leaf node if it exceeds the order
        if (newKeys.size > order) {
          val mid = newKeys.size / 2
          val leftKeys = newKeys.take(mid)
          val rightKeys = newKeys.drop(mid)
          val leftValues = newValues.take(mid)
          val rightValues = newValues.drop(mid)
          val rightLeaf = LeafNode(rightKeys, rightValues, next)
          val leftLeaf = LeafNode(leftKeys, leftValues, Some(rightLeaf))
          (leftLeaf, Some(rightKeys.head, rightLeaf))
        } else (LeafNode(newKeys, newValues, next), None) // No split, no need to update the parent

      case InternalNode(keys, children) =>
        val idx = keys.indexWhere(implicitly[Ordering[K]].gt(_, key)) match {
          case -1 => keys.size
          case i => i
        }

        // Recursively insert into the child node
        val (updatedChild, split) = insertNode(children(idx))// split is the key-value pair to be inserted into the parent node
        split match {
          case None =>
            (InternalNode(keys, children.updated(idx, updatedChild)), None)
          case Some((splitKey, splitNode)) =>
            val (newKeys, newChildren) = 
              keys.splitAt(idx) match {
                case (beforeKeys, afterKeys) =>
                  ((beforeKeys :+ splitKey) ++ afterKeys, children.splitAt(idx)._1 :+ updatedChild :+ splitNode)
              }
            if (newKeys.size > order) {
              val mid = newKeys.size / 2
              val leftKeys = newKeys.take(mid)
              val rightKeys = newKeys.drop(mid + 1)
              val leftChildren = newChildren.take(mid + 1)
              val rightChildren = newChildren.drop(mid + 1)
              val rightNode: Node[K, V] = InternalNode(rightKeys, rightChildren)
              (InternalNode(leftKeys, leftChildren), Some(newKeys(mid), rightNode))
            } else (InternalNode(newKeys, newChildren), None)
        }
    }

    val (newRoot, split) = insertNode(root)
    
    val newTreeRoot = split match {
      case Some((splitKey, splitNode)) => InternalNode(Vector(splitKey), Vector(newRoot, splitNode))
      case None => newRoot
    }
    new BPlusTree(order, newTreeRoot)
  }

  def delete(key: K): BPlusTree[K, V] = {
    def deleteNode(node: Node[K, V]): (Node[K, V], Boolean) = node match {
      case LeafNode(keys, values, next) =>
        keys.indexWhere(implicitly[Ordering[K]].equiv(_, key)) match {
          case -1 => (node, false)
          case idx =>
            val newKeys = keys.take(idx) ++ keys.drop(idx + 1)
            val newValues = values.take(idx) ++ values.drop(idx + 1)
            (LeafNode(newKeys, newValues, next), newKeys.size < order / 2)
        }

      case InternalNode(keys, children) =>
        val idx = keys.indexWhere(implicitly[Ordering[K]].gt(_, key)) match {
          case -1 => keys.size
          case i => i
        }
        val (updatedChild, underflow) = deleteNode(children(idx))
        if (!underflow) {
          (InternalNode(keys, children.updated(idx, updatedChild)), false)
        } else {
          // Handle underflow
          val (newKeys, newChildren) = if (idx > 0 && children(idx - 1).asInstanceOf[LeafNode[K, V]].keys.size > order / 2) {
            val leftSibling = children(idx - 1).asInstanceOf[LeafNode[K, V]]
            val borrowedKey = leftSibling.keys.last
            val borrowedValue = leftSibling.values.last
            val newLeftSibling = LeafNode(leftSibling.keys.dropRight(1), leftSibling.values.dropRight(1), leftSibling.next)
            val newUpdatedChild = updatedChild.asInstanceOf[LeafNode[K, V]].copy(keys = borrowedKey +: updatedChild.asInstanceOf[LeafNode[K, V]].keys, values = borrowedValue +: updatedChild.asInstanceOf[LeafNode[K, V]].values)
            (keys.updated(idx - 1, borrowedKey), children.updated(idx - 1, newLeftSibling).updated(idx, newUpdatedChild))
          } else if (idx < keys.size && children(idx + 1).asInstanceOf[LeafNode[K, V]].keys.size > order / 2) {
            val rightSibling = children(idx + 1).asInstanceOf[LeafNode[K, V]]
            val borrowedKey = rightSibling.keys.head
            val borrowedValue = rightSibling.values.head
            val newRightSibling = LeafNode(rightSibling.keys.tail, rightSibling.values.tail, rightSibling.next)
            val newUpdatedChild = updatedChild.asInstanceOf[LeafNode[K, V]].copy(keys = updatedChild.asInstanceOf[LeafNode[K, V]].keys :+ borrowedKey, values = updatedChild.asInstanceOf[LeafNode[K, V]].values :+ borrowedValue)
            (keys.updated(idx, borrowedKey), children.updated(idx + 1, newRightSibling).updated(idx, newUpdatedChild))
          } else {
            // Merge with sibling
            if (idx > 0) {
              val leftSibling = children(idx - 1).asInstanceOf[LeafNode[K, V]]
              val mergedKeys = leftSibling.keys ++ updatedChild.asInstanceOf[LeafNode[K, V]].keys
              val mergedValues = leftSibling.values ++ updatedChild.asInstanceOf[LeafNode[K, V]].values
              val newLeftSibling = LeafNode(mergedKeys, mergedValues, updatedChild.asInstanceOf[LeafNode[K, V]].next)
              (keys.take(idx - 1) ++ keys.drop(idx), children.take(idx - 1) ++ Vector(newLeftSibling) ++ children.drop(idx + 1))
            } else {
              val rightSibling = children(idx + 1).asInstanceOf[LeafNode[K, V]]
              val mergedKeys = updatedChild.asInstanceOf[LeafNode[K, V]].keys ++ rightSibling.keys
              val mergedValues = updatedChild.asInstanceOf[LeafNode[K, V]].values ++ rightSibling.values
              val newRightSibling = LeafNode(mergedKeys, mergedValues, rightSibling.next)
              (keys.take(idx) ++ keys.drop(idx + 1), children.take(idx) ++ Vector(newRightSibling) ++ children.drop(idx + 2))
            }
          }
          (InternalNode(newKeys, newChildren), newKeys.size < order / 2)
        }
    }

    val (newRoot, underflow) = deleteNode(root)
    val newTreeRoot = if (underflow && newRoot.isInstanceOf[InternalNode[K, V]] && newRoot.asInstanceOf[InternalNode[K, V]].children.size == 1) {
      newRoot.asInstanceOf[InternalNode[K, V]].children.head
    } else {
      newRoot
    }
    new BPlusTree(order, newTreeRoot)
  }

  def printTree(): Unit = {
    def printNode(node: Node[K, V], level: Int): Unit = {
      val indent = " " * level * 2
      node match {
        case LeafNode(keys, values, _) =>
          println(s"$indent Leaf(keys: $keys, values: $values)")
        case InternalNode(keys, children) =>
          println(s"$indent Internal(keys: $keys)")
          children.foreach(child => printNode(child, level + 1))
      }
    }
    printNode(root, 0)
  }
}

// Test
object BPlusTreeDemo extends App {
  var bpt = new BPlusTree[Int, String](2)
  bpt = bpt.insert(10, "Ten")
  bpt = bpt.insert(20, "Twenty")
  bpt = bpt.insert(5, "Five")

  println("B+ Tree Structure:")
  bpt.printTree()

  bpt = bpt.insert(6, "Six")
  bpt = bpt.insert(15, "Fifteen")

  println("B+ Tree Structure:")
  bpt.printTree()

  println("\nSearch Test:")
  println(s"Search key 10: ${bpt.search(10)}")
  println(s"Search key 15: ${bpt.search(15)}")
  println(s"Search key 100: ${bpt.search(100)}")

  println("\nDelete Test:")
  bpt = bpt.delete(6)
  bpt = bpt.delete(5)
  bpt.printTree()
}