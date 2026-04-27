import SP1Foundations
import SP1Operations.Operation.U16MSBOperation

structure SubwOperation where
  value : Vector (Fin KB) 2
  msb : U16MSBOperation (Fin KB)
