import SP1Foundations
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation

structure AddwOperation (F : Type) where
  value : Vector F 2
  msb : U16MSBOperation F
