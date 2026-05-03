import SP1Foundations
import SP1Operations.Operation.AddrAddOperation.Operation

structure AddressOperation (F : Type) where
  addr_operation : AddrAddOperation F
  top_two_limb_inv : F
