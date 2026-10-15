import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.Model.Core.ProgramImage
import SP1Clean.Model.Semantics.Decode

/-! # Public boot boundary of the image-authenticated native core

The native verifier fixes the initial clock to one and the initial PC to the checked image's
entry point. The existing public-limb contract supplies canonical encodings of both endpoints.
These are constraints of the native verifier, not a caller-supplied loader or commitment premise.
-/

namespace SP1Clean.SP1PublicIO

open SP1Clean.Model.Core SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime]

def BootFor (image : ProgramImage) (pi : SP1PublicIO (ZMod p)) : Prop :=
  pi.init_clk_high = 0 ∧ pi.init_clk_low = 1 ∧
    pi.init_pc0 = (bitVecToWord image.entry)[0] ∧
    pi.init_pc1 = (bitVecToWord image.entry)[1] ∧
    pi.init_pc2 = (bitVecToWord image.entry)[2]

end SP1Clean.SP1PublicIO
