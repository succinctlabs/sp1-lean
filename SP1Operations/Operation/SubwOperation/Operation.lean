import SP1Foundations
import SP1Operations.Operation.U16MSBOperation

structure SubwOperation where
  value : Vector (Fin BB) 2
  msb : U16MSBOperation
