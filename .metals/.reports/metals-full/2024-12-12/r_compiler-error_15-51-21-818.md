file://<WORKSPACE>/Test/tests.scala
### java.lang.IndexOutOfBoundsException: -1

occurred in the presentation compiler.

presentation compiler configuration:


action parameters:
offset: 774
uri: file://<WORKSPACE>/Test/tests.scala
text:
```scala
import bplus_stainless.*
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.proof._
import stainless.lang.Map.ToMapOps
import stainless.collection.ListSpecs._

object Tests extends App{
  val testLeaf = LeafNode[String](List[(BigInt, String)]((1, "one"), (2, "two"), (3, "three"), (4, "four"), (6, "six")), 10, None[LeafNode[String]]())
  val order1 = List[BigInt](1,3,5,7,10)
  val order2 = List[BigInt](4,1,2,6,10,9)
  val order3 = List[BigInt](5,5,5,5,5,5,5,6)
  val testInsertLeaf = LeafNode[String](List[(BigInt, String)]((1, "one"), (2, "two"), (3, "three"), (4, "four"), (6, "six"), (7, "seven")), 6, None[LeafNode[String]]())
  val testInsertLeaf2 = LeafNode[String](List[(BigInt, String)]( (5, "five"), (6, "six"), @@), 6, None[LeafNode[String]]())
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
    assert(!isOrdered(order3))
  }

  def insertNoSplitTests(): Unit = {
    assert(testLeaf.insertNoSplit(5, "five") ==  LeafNode[String](List[(BigInt, String)]((1, "one"), (2, "two"), (3, "three"), (4, "four"), (5, "five"), (6, "six")), 10, None[LeafNode[String]]()))
  }

  def insertSplitTests(): Unit = {
    println(testInsertLeaf.insertSplit(5, "five"))
    println(testInsertLeaf1)
    println(testInsertLeaf2)
    assert(testInsertLeaf.insertSplit(5, "five")==(testInsertLeaf1, testInsertLeaf2))
  }
  println("hello")
  insertNoSplitTests()
  insertSplitTests()
  //stainless can't handle this test - see how to do tests with the TAs
}

```



#### Error stacktrace:

```
scala.collection.LinearSeqOps.apply(LinearSeq.scala:129)
	scala.collection.LinearSeqOps.apply$(LinearSeq.scala:128)
	scala.collection.immutable.List.apply(List.scala:79)
	dotty.tools.dotc.util.Signatures$.applyCallInfo(Signatures.scala:244)
	dotty.tools.dotc.util.Signatures$.computeSignatureHelp(Signatures.scala:101)
	dotty.tools.dotc.util.Signatures$.signatureHelp(Signatures.scala:88)
	dotty.tools.pc.SignatureHelpProvider$.signatureHelp(SignatureHelpProvider.scala:47)
	dotty.tools.pc.ScalaPresentationCompiler.signatureHelp$$anonfun$1(ScalaPresentationCompiler.scala:422)
```
#### Short summary: 

java.lang.IndexOutOfBoundsException: -1