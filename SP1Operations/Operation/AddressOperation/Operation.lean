import SP1Foundations
import SP1Operations.Operation.AddrAddOperation.Operation

structure AddressOperation where
  addr_operation : AddrAddOperation (Fin KB)
  top_two_limb_inv : Fin KB
