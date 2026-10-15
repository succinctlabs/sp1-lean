import SP1Clean.Model.Core.HintQueueWordRecords

/-! # Immutable hint-word coordination

The channel carries the node identity, word position, full value, and final-word marker. Its guarantee is only
local representation validity. Source and authorized-allocation providers must establish actual
byte binding; complete consumers must request every required word, including final padding.
-/

namespace SP1Clean.HostHintQueue

open Circuit Model.Core.HintQueue

def wordChannel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) WordRecord where
  name := "sp1.native.hint_word"
  Guarantees record _ := record.Valid

end SP1Clean.HostHintQueue
