import SP1Foundations
import SP1Operations.Operation.U16MSBOperation

structure AddwOperation where
  value : Vector (Fin KB) 2
  msb : U16MSBOperation
