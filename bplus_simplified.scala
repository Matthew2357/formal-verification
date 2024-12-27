sealed trait Node[K, V]
case class InternalNode[K, V](keys: Vector[K], children: Vector[Node[K, V]]) extends Node[K, V]
case class LeafNode[K, V](keys: Vector[K], values: Vector[V], next: Option[LeafNode[K, V]]) extends Node[K, V]

class BPlusTree[K: Ordering, V](val order: Int, val root: Node[K, V] = LeafNode[K, V](Vector.empty, Vector.empty, None)) {
  private val ord = implicitly[Ordering[K]]

  def insert(key: K, value: V): BPlusTree[K, V] = {
    def insertLeaf(leaf: LeafNode[K, V]): (Node[K, V], Option[(K, Node[K, V])]) = {
      val insertPos = leaf.keys.indexWhere(ord.gt(_, key)) match {
        case -1 => leaf.keys.size
        case i => i
      }
      
      val newKeys = leaf.keys.take(insertPos) ++ Vector(key) ++ leaf.keys.drop(insertPos)
      val newValues = leaf.values.take(insertPos) ++ Vector(value) ++ leaf.values.drop(insertPos)

      if (newKeys.size <= order) {
        (LeafNode(newKeys, newValues, leaf.next), None)
      } else {
        val splitPoint = newKeys.size / 2
        val leftKeys = newKeys.take(splitPoint)
        val rightKeys = newKeys.drop(splitPoint)
        val leftValues = newValues.take(splitPoint)
        val rightValues = newValues.drop(splitPoint)
        
        val rightNode = LeafNode(rightKeys, rightValues, leaf.next)
        val leftNode = LeafNode(leftKeys, leftValues, Some(rightNode))
        
        (leftNode, Some((rightKeys.head, rightNode)))
      }
    }

    def insertInternal(node: InternalNode[K, V], key: K, value: V): (Node[K, V], Option[(K, Node[K, V])]) = {
      val childIndex = node.keys.indexWhere(ord.gt(_, key)) match {
        case -1 => node.keys.size
        case i => i
      }

      val child = node.children(childIndex)
      val (newChild, splitInfo) = child match {
        case leaf: LeafNode[K, V] => insertLeaf(leaf)
        case internal: InternalNode[K, V] => insertInternal(internal, key, value)
      }

      splitInfo match {
        case None =>
          (InternalNode(node.keys, node.children.updated(childIndex, newChild)), None)
        
        case Some((splitKey, splitNode)) =>
          val newKeys = node.keys.take(childIndex) ++ Vector(splitKey) ++ node.keys.drop(childIndex)
          val newChildren = node.children.take(childIndex) ++ Vector(newChild, splitNode) ++ node.children.drop(childIndex + 1)

          if (newKeys.size <= order - 1) {
            (InternalNode(newKeys, newChildren), None)
          } else {
            val splitPoint = newKeys.size / 2
            val leftKeys = newKeys.take(splitPoint)
            val rightKeys = newKeys.drop(splitPoint + 1)
            val leftChildren = newChildren.take(splitPoint + 1)
            val rightChildren = newChildren.drop(splitPoint + 1)
            
            val splitKey = newKeys(splitPoint)
            val leftNode = InternalNode(leftKeys, leftChildren)
            val rightNode = InternalNode(rightKeys, rightChildren)
            
            (leftNode, Some((splitKey, rightNode)))
          }
      }
    }

    val (newRoot, splitInfo) = root match {
      case leaf: LeafNode[K, V] => insertLeaf(leaf)
      case internal: InternalNode[K, V] => insertInternal(internal, key, value)
    }

    splitInfo match {
      case None => new BPlusTree(order, newRoot)
      case Some((splitKey, splitNode)) =>
        new BPlusTree(order, InternalNode(Vector(splitKey), Vector(newRoot, splitNode)))
    }
  }
}
