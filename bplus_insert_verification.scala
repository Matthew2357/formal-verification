import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object BPlusTreeVerification {
  val MIN_ORDER: BigInt = 3
  val ORDER: BigInt = MIN_ORDER // Define ORDER as fixed MIN_ORDER

  // Core invariants
  sealed abstract class Tree {
    
    def content: List[BigInt] = {
      require(isValidTree(this, true))
      decreases(
    
      measureHelper(this), this.size
    )

      this match {
        case Leaf(keys, _) => keys
        case Internal(keys, children) =>
          if (children.isEmpty) keys
          else {
            // Ensure currentHeight decreases for each child
            children.foldLeft(List[BigInt]()) { (acc, c) =>
              //require(currentHeight - 1 >= insertMeasure(c, true)) // Add requirement
              acc ++ c.content
            }
          }
      }
    }

    def size: BigInt = {
      
      this match {
      case Leaf(keys, _) => keys.size
      case Internal(_, children) => max(0,1 + children.map(_.size).foldLeft(BigInt(0))(_ + _))
    }
  }.ensuring(res => res >= 0)

  }

  case class Leaf(keys: List[BigInt], values: List[BigInt]) extends Tree {
    require(keys.size == values.size) // Ensures keys and values are always in sync
  }
  case class Internal(keys: List[BigInt], children: List[Tree]) extends Tree {
    require(keys.nonEmpty && children.size == keys.size + 1)
  }

  // Basic validity checks
  def isValidTree(t: Tree, isRoot: Boolean): Boolean = { // Removed 'order' parameter
    require(ORDER >= MIN_ORDER) // Ensure ORDER is not less than MIN_ORDER
    t match {
      case Leaf(keys, values) => 
        keys.size == values.size &&
        isValidSize(keys.size, isRoot) &&
        isSorted(keys)
      case Internal(keys, children) =>
        keys.nonEmpty &&
        children.size == keys.size + 1 &&
        isValidSize(keys.size, isRoot) &&
        isSorted(keys) &&
        children.forall(c => isValidTree(c, false))
    }
  }.ensuring(res => res ==> (!t.isInstanceOf[Internal] || t.asInstanceOf[Internal].children.forall(c => isValidTree(c, false))))

  def sameLengths(t: Tree, isRoot: Boolean): Boolean = {
    require(isValidTree(t, isRoot))
    decreases(
      measureHelper(t), insertMeasure(t, isRoot)
    )
    val im = insertMeasure(t, isRoot)
    t match {
      case Leaf(keys, values) => true
      case Internal(keys, children) => 
        (keys, children) match {
          case (_, Nil()) => true
          case (keyss, Cons(head, tail)) => 
            
            val newKeys = if(keyss.length==1){Nil[BigInt]()}else{keys.init}
            val headMeasure = sameLengths(head, false)
            val tempNode = Internal(newKeys, tail)
            
            insertMeasure(head, false) == insertMeasure(tempNode, isRoot) && sameLengths(head, false)
        }
    }
  }.ensuring(res => res == (!t.isInstanceOf[Internal] || t.asInstanceOf[Internal].children.forall(c => sameLengths(c, false) )))

  def lengthsLemma(t:Internal): Unit = {
    require(isValidTree(t, false) && sameLengths(t, false))
  }.ensuring(_=>t.children.forall(c => insertMeasure(c, false)==insertMeasure(t, false)-1))
  
  def isValidSize(size: BigInt, isRoot: Boolean): Boolean = { // Removed 'order' parameter
    if (isRoot) size <= ORDER
    else size >= (ORDER + 1) / 2 && size <= ORDER
  }

  def isSorted(keys: List[BigInt]): Boolean = {
    decreases(keys)
    keys match {
      case Nil() => true
      case Cons(_, Nil()) => true
      case Cons(x, l @ Cons(y, _)) => x < y && isSorted(l)
    }
  }


  def valueContent(t: Tree): List[BigInt] = {
      require(isValidTree(t, true))
      decreases(
    
      measureHelper(t), t.size
    )

      t match {
        case Leaf(_, values) => values
        case Internal(keys, children) =>
          if (children.isEmpty) List[BigInt]()
          else {
            // Ensure currentHeight decreases for each child
            children.foldLeft(List[BigInt]()) { (acc, c) =>
              //require(currentHeight - 1 >= insertMeasure(c, true)) // Add requirement
              acc ++ valueContent(c)
          }
      }
    }
  }




  // Add custom max function for BigInt
  def max(x: BigInt, y: BigInt): BigInt = {
    if (x > y) x else y
  }

  def insertMeasure(t: Tree, isRoot: Boolean): BigInt = {
  require(isValidTree(t, isRoot))
  decreases(
    
      measureHelper(t), t.size
    )

  t match {
    case Leaf(keys, values) => BigInt(1)
    case Internal(keys, children) => 
      (keys, children) match {
        case (_, Nil()) => BigInt(1)
        case (keyss, Cons(head, tail)) => 
          val newKeys = if(keyss.length==1){Nil[BigInt]()}else{keys.init}
          val headMeasure = insertMeasure(head, false)
          val tempNode = Internal(newKeys, tail)
          max(headMeasure, insertMeasure(tempNode, isRoot))+1
      }
  }
}.ensuring(res => res >= 1  &&
 (!t.isInstanceOf[Internal] || t.asInstanceOf[Internal].children.forall(c => insertMeasure(c, false) < res)))

  def measureHelper(t: Tree): BigInt = {
    t match {
      case Internal(_, children) => children.length
      case Leaf(keys, values) => BigInt(0) 
    }
  }


  
  def insert(tree: Tree, key: BigInt, value: BigInt, isRoot: Boolean): Tree = {
    require(
      ORDER == MIN_ORDER && // Ensure ORDER is not less than MIN_ORDER
      isValidTree(tree, isRoot) && sameLengths(tree, isRoot) &&
      insertMeasure(tree, isRoot) >= 0
      && !valueContent(tree).contains(value)
    )
    decreases(insertMeasure(tree, isRoot))
    
    val result = tree.match {
      case leaf @ Leaf(keys, values) =>
        // Added check for empty Leaf
        if (!keys.isEmpty) {
          
          assert(insertMeasure(leaf, isRoot) >= 0)
          
         
          
        }
        if (keys.isEmpty) {
          insertIntoLeaf(leaf, key, value)
        } else if (contains(leaf, key, isRoot)) {
          leaf
        } else if (keys.size < ORDER) { 
          
          insertIntoLeaf(leaf, key, value)
        } else {
          assert(ORDER == MIN_ORDER)
          assert(isSorted(leaf.keys))
          assert(!leaf.keys.contains(key))
          assert(leaf.keys.size==ORDER)
          
          
          
          val res = splitLeaf(leaf, key, value) // Removed 'order' parameter
          assert(isValidTree(res, isRoot))
          assert(sameLengths(res, isRoot))
          res
        }

      case internal @ Internal(keys, children) =>
        internalChildrenCountLemmaCorrect(internal, false) // Removed 'order' parameter
        val pos = findPosition(keys, key)
        val newChild = insert(children(pos), key, value, false)  // Recursive call without 'order'
        lengthsLemma(internal)
        balanceInternal(internal, newChild, pos) // Removed 'order' parameter
    }

    // Ensure insertMeasureInvariant holds for the result
    result
  }.ensuring(res => 
    isValidTree(res, isRoot) && sameLengths(res, isRoot) &&
    insertMeasure(res, isRoot) >= 0
  )

  
  
  @opaque
  def contains(tree: Tree, key: BigInt, isRoot: Boolean): Boolean = {
    require(
      isValidTree(tree, true) &&//&& sameLengths(tree, isRoot) &&
      insertMeasure(tree, true) >= 0 &&
      
      // Add requirement that internal nodes have valid children count
      (!tree.isInstanceOf[Internal] || 
        tree.asInstanceOf[Internal].children.size == tree.asInstanceOf[Internal].keys.size + 1)
    )
    decreases(insertMeasure(tree, true))
    
    tree match {
      case Leaf(keys, _) =>
        if (keys.isEmpty) false 
        else {
          // Strengthen the containment check
          val res:Boolean = keys.contains(key)
          assert(res == tree.content.contains(key))
          res
        }
      case internal @ Internal(keys, children) =>
        val pos = findPosition(keys, key)
        if (pos < keys.size && keys(pos) == key) {
          assert(tree.content.contains(key))
          true
        } else if (pos < children.size) {
          // Add measure decrease assertion
          assert(insertMeasure(children(pos), true) < insertMeasure(tree, true))
          contains(children(pos), key, true)
        } else false
    }
  }.ensuring(res => res == tree.content.contains(key))

  // Added a helper function to accurately compute the expected result
  
  // Ensures the postcondition aligns with the actual content of the tree

  // Make findPosition public
  def findPosition(keys: List[BigInt], key: BigInt): BigInt = {
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
      leaf.keys.size < MIN_ORDER // Prevent insertion when order constraints are violated
    )
    val pos = findPosition(leaf.keys, key)
    Leaf(
      leaf.keys.take(pos) ++ List(key) ++ leaf.keys.drop(pos),
      leaf.values.take(pos) ++ List(value) ++ leaf.values.drop(pos)
    )
  }

  // Split operations
  @opaque
  private def splitLeaf(leaf: Leaf, key: BigInt, value: BigInt): Tree = { // Removed 'order' parameter
    require(
      ORDER == MIN_ORDER && // Enforce ORDER >= MIN_ORDER
      isSorted(leaf.keys) &&
      // Added explicit check for missing key
      !leaf.keys.contains(key) &&
      leaf.keys.size == ORDER && // Replaced 'order' with 'ORDER'
      // Add measure invariant requirement
      insertMeasure(leaf, true) >= 0
      && !leaf.values.contains(value) // Ensure value is not already present
    )
    
    val pos = findPosition(leaf.keys, key)
    val newKeys = insertIntoSorted(leaf.keys, key)
    assert(isSorted(newKeys))
    val mid = ORDER / 2

    // Create new internal node with split leaves
    val result = Internal(
      List(newKeys(mid)),
      List(
        Leaf(newKeys.take(mid), leaf.values.take(mid)),
        Leaf(newKeys.drop(mid + 1), leaf.values.drop(mid))
      )
    )
    
    // Verify result properties
    assert(isSorted(result.asInstanceOf[Internal].keys))
    assert(result.isInstanceOf[Internal])
    result
  }.ensuring(res => 
    res.isInstanceOf[Internal] &&
    isSorted(res.asInstanceOf[Internal].keys) &&
    insertMeasure(res, true) == 2 && res.asInstanceOf[Internal].children.forall(c => insertMeasure(c, false)==1) 
    && valueContent(res).contains(value)

  )

  // Simplify balanceInternal preconditions
  @opaque
  private def balanceInternal(node: Internal, newChild: Tree, pos: BigInt): Tree = { // Removed 'order' parameter
    require(
      ORDER >= MIN_ORDER && // Enforce ORDER >= MIN_ORDER
      pos >= 0 && pos < node.children.size &&
      isSorted(node.keys) &&
      isValidTree(newChild, false) && 
      isValidTree(node, true) && insertMeasure(newChild, false)==insertMeasure(node, true)-1
      
    )

    newChild match {
      case Internal(splitKeys, splitChildren) if splitKeys.size == 1 =>
        if (node.keys.size < ORDER - 1) { // Replaced 'order' with 'ORDER'
          // Simple merge
          Internal(
            node.keys.take(pos) ++ splitKeys ++ node.keys.drop(pos),
            node.children.take(pos) ++ splitChildren ++ node.children.drop(pos + 1)
          )
        } else {
          // Need to split internal node
          val allKeys = node.keys.take(pos) ++ splitKeys ++ node.keys.drop(pos)
          val allChildren = node.children.take(pos) ++ splitChildren ++ node.children.drop(pos + 1)
          val mid = ORDER / 2 // Replaced 'order' with 'ORDER'
          
          Internal(
            List(allKeys(mid)),
            List(
              Internal(allKeys.take(mid), allChildren.take(mid + 1)),
              Internal(allKeys.drop(mid + 1), allChildren.drop(mid + 1))
            )
          )
        }
      case _ =>
        
        val res = Internal(node.keys, node.children.updated(pos, newChild))
        assert(res.keys.nonEmpty)
        assert(res.children.size==res.keys.size+1)
        assert(isValidSize(res.keys.size, false)) 
        assert(isSorted(res.keys))
        assert(res.children.forall(c=>isValidTree(c,false))) 
        
        res
    }
  }.ensuring(res => 
    isValidTree(res, false) && sameLengths(res, false)
  ) 

  // Helper functions for list operations
  // Make insertIntoSorted public
  def insertIntoSorted(keys: List[BigInt], key: BigInt): List[BigInt] = {
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


  @opaque
  // Lemma to handle internalChildrenCountLemma
  def internalChildrenCountLemmaCorrect(t: Tree, isRoot: Boolean): Boolean = {
    require(isValidTree(t, isRoot) && sameLengths(t, isRoot) && t.isInstanceOf[Internal])
    val i = t.asInstanceOf[Internal]
    i.children.size == i.keys.size + 1
  }.holds

  
  

}




