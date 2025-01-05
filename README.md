# Formal Verification project

In this project we implement insertion on a B+ Tree in Scala, which we then verify using Stainless. 

To run, use the command  ```stainless bplus_insert_verification.scala```. It takes about 3 minutes to run.

The order (fanout) of the tree is fixed at the beginning of the file. Setting ORDER=2 makes the program run in 1 minute, whereas ORDER=4 takes at least an hour (we didn't try and wait longer).
