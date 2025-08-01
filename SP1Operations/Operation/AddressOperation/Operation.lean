import SP1Foundations
import SP1Operations.Operation.AddrAddOperation.Operation

structure AddressOperation where
  addr_word_operation : AddrAddOperation
  top_two_limb_inv : Fin BB
