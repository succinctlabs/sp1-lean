import SP1Clean.Model.Semantics.GuestProgram
import Clean.Circuit.Expression

/-! # The program commitment — `ProverData` as the committed guest program

The machine-grounding design keys every global execution/decode claim to **the deterministic execution
of the committed program**: the prover writes the guest program into `ProverData` (Clean's committed
prover-data store, `String → (n : ℕ) → Array (Vector F n)`, shared across all tables of an ensemble
witness via `same_data`), and `progOf` decodes it back to a `GuestProgram`. Binding the committed data
to *the* program of interest is the `StatementFor` conjunct `progOf witness.data = prog` — the Lean
shadow of SP1's verifying-key program commitment. Channel guarantees themselves remain row-local and
structural; this binding is consumed by the global Program/State grounding theorems.

Reserved keys (arities pinned by the decoders below):
- `"sp1.rom"`, arity 5 — one instruction per row: `[pc0, pc1, pc2, w_lo, w_hi]` (pc as three 16-bit
  limbs, the 32-bit encoding as two 16-bit halves);
- `"sp1.pc_start"`, arity 3 — the entry point's three 16-bit limbs;
- `"sp1.image"`, arity 4 — one byte per row: `[a0, a1, a2, byte]` (48-bit address limbs, one byte);
- `"sp1.init_clk"`, arity 2 — the genesis clock `[clk_high, clk_low]`.

`progOf` is **total** via sanitization — duplicate ROM addresses are dropped (keep-first),
misaligned addresses removed, out-of-window addresses removed, and compressed (non-full-width)
entries removed, so all four `GuestProgram` guards
(`rom_nodup`/`rom_aligned`/`rom_in_window`/`rom_full_width`) hold by construction and a
malicious `data` still decodes to *some* well-formed program (the guarantees are then statements about
that program). Headline AIR relations additionally require `StatementFor`: the raw representation must
be canonical, so sanitization/truncation cannot hide malformed committed data, and `progOf data` equals
the public program. -/

namespace SP1Clean.Commit

open SP1Clean.Soundness.Target

variable {p : ℕ}

/-! ## ROM sanitization -/

/-- Keep-first dedup by address + drop misaligned entries, so the decoded ROM is a well-formed
`GuestProgram.rom` regardless of what the prover committed. -/
def sanitizeRom : List (BitVec 64 × BitVec 32) → List (BitVec 64 × BitVec 32)
  | [] => []
  | e :: rest =>
    if e.1.toNat % 4 = 0 ∧ 2 ^ 16 ≤ e.1.toNat ∧ e.1.toNat + 4 ≤ 2 ^ 48
        ∧ e.2.extractLsb' 0 2 = 0b11#2 then
      e :: (sanitizeRom rest).filter (fun e' => e'.1 ≠ e.1)
    else
      sanitizeRom rest

theorem sanitizeRom_nodup (l : List (BitVec 64 × BitVec 32)) :
    ((sanitizeRom l).map Prod.fst).Nodup := by
  induction l with
  | nil => simp [sanitizeRom]
  | cons e rest ih =>
    rw [sanitizeRom]
    split
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih.sublist (List.filter_sublist.map Prod.fst)⟩
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hmem
      have hne := List.of_mem_filter he'
      simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at hne
      exact hne heq
    · exact ih

theorem sanitizeRom_aligned (l : List (BitVec 64 × BitVec 32)) :
    ∀ a ∈ (sanitizeRom l).map Prod.fst, a.toNat % 4 = 0 := by
  induction l with
  | nil => simp [sanitizeRom]
  | cons e rest ih =>
    rw [sanitizeRom]
    split
    · rename_i hguard
      intro a ha
      rcases List.mem_map.mp ha with ⟨e', he', rfl⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact hguard.1
      · exact ih _ (List.mem_map_of_mem (List.mem_of_mem_filter he'))
    · exact ih

/-- Every sanitized ROM entry sits in the SP1 code window `[2^16, 2^48)` — the sanitizer drops entries
outside it, so `rom_in_window` holds by construction. -/
theorem sanitizeRom_in_window (l : List (BitVec 64 × BitVec 32)) :
    ∀ aw ∈ sanitizeRom l, 2 ^ 16 ≤ aw.1.toNat ∧ aw.1.toNat + 4 ≤ 2 ^ 48 := by
  induction l with
  | nil => simp [sanitizeRom]
  | cons e rest ih =>
    rw [sanitizeRom]
    split
    · rename_i hguard
      intro aw haw
      rcases List.mem_cons.mp haw with rfl | haw
      · exact ⟨hguard.2.1, hguard.2.2.1⟩
      · exact ih _ (List.mem_of_mem_filter haw)
    · exact ih

/-- Every sanitized ROM word is a full 32-bit (non-compressed) instruction (low two bits `0b11`) — the
sanitizer drops compressed entries, so `rom_full_width` holds by construction. -/
theorem sanitizeRom_full_width (l : List (BitVec 64 × BitVec 32)) :
    ∀ aw ∈ sanitizeRom l, aw.2.extractLsb' 0 2 = 0b11#2 := by
  induction l with
  | nil => simp [sanitizeRom]
  | cons e rest ih =>
    rw [sanitizeRom]
    split
    · rename_i hguard
      intro aw haw
      rcases List.mem_cons.mp haw with rfl | haw
      · exact hguard.2.2.2
      · exact ih _ (List.mem_of_mem_filter haw)
    · exact ih

/-! ## The per-row decoders -/

/-- One committed ROM row `[pc0, pc1, pc2, w_lo, w_hi]` → `(pc, instruction word)`. The pc limbs are
`val`-recombined base-2^16 (matching the Program-bus pc limb convention); the word halves likewise. -/
def romEntryOf (v : Vector (ZMod p) 5) : BitVec 64 × BitVec 32 :=
  (BitVec.ofNat 64 (v[0].val + v[1].val * 2 ^ 16 + v[2].val * 2 ^ 32),
   BitVec.ofNat 32 (v[3].val % 2 ^ 16 + (v[4].val % 2 ^ 16) * 2 ^ 16))

/-- One committed image row `[a0, a1, a2, byte]` → `(address, byte)`. -/
def imageEntryOf (v : Vector (ZMod p) 4) : BitVec 64 × BitVec 8 :=
  (BitVec.ofNat 64 (v[0].val + v[1].val * 2 ^ 16 + v[2].val * 2 ^ 32),
   BitVec.ofNat 8 (v[3].val % 2 ^ 8))

/-- The raw committed rows, before totalizing/sanitizing their semantic decoder. -/
def romRowsOf (data : ProverData (ZMod p)) : List (Vector (ZMod p) 5) :=
  (data "sp1.rom" 5).toList

def imageRowsOf (data : ProverData (ZMod p)) : List (Vector (ZMod p) 4) :=
  (data "sp1.image" 4).toList

def pcStartRowsOf (data : ProverData (ZMod p)) : List (Vector (ZMod p) 3) :=
  (data "sp1.pc_start" 3).toList

def initClockRowsOf (data : ProverData (ZMod p)) : List (Vector (ZMod p) 2) :=
  (data "sp1.init_clk" 2).toList

/-- Every field cell is the canonical representative of a limb of the requested width. -/
def RowValuesBelow {n : ℕ} (bound : ℕ) (row : Vector (ZMod p) n) : Prop :=
  ∀ value ∈ row.toList, value.val < bound

/-- The committed entry point (`0` if the key is absent/malformed — the vkey binding pins the honest
value). -/
def pcStartOf (data : ProverData (ZMod p)) : BitVec 64 :=
  match (data "sp1.pc_start" 3).toList with
  | [v] => BitVec.ofNat 64 (v[0].val + v[1].val * 2 ^ 16 + v[2].val * 2 ^ 32)
  | _ => 0

/-- The committed genesis clock, ℕ-decoded (`1` if absent/malformed, keeping `1 ≤ initClkNat` the
honest default the boundary vkey assumption also carries). -/
def initClkNat (data : ProverData (ZMod p)) : ℕ :=
  match (data "sp1.init_clk" 2).toList with
  | [v] => v[0].val * 2 ^ 24 + v[1].val
  | _ => 1

/-- **The committed guest program.** Total: sanitization makes `rom_nodup`/`rom_aligned` hold by
construction, so every `ProverData` decodes to a well-formed program. -/
def progOf (data : ProverData (ZMod p)) : GuestProgram where
  rom := sanitizeRom ((romRowsOf data).map romEntryOf)
  pc_start := pcStartOf data
  memImage := (imageRowsOf data).map imageEntryOf
  rom_nodup := sanitizeRom_nodup _
  rom_aligned := sanitizeRom_aligned _
  rom_in_window := sanitizeRom_in_window _
  rom_full_width := sanitizeRom_full_width _

/-! ## Canonical statement binding -/

/-- The committed representation is injective at the decoder boundary: no ROM row is discarded by
sanitization, all byte/16-bit limbs are in range rather than silently reduced, singleton keys really
are singletons, and image addresses are unique. -/
def CanonicalEncoding (data : ProverData (ZMod p)) : Prop :=
  let rawRom := (romRowsOf data).map romEntryOf
  let rawImage := (imageRowsOf data).map imageEntryOf
  sanitizeRom rawRom = rawRom ∧
  (∀ row ∈ romRowsOf data, RowValuesBelow (2 ^ 16) row) ∧
  (∀ row ∈ imageRowsOf data,
    row[0].val < 2 ^ 16 ∧ row[1].val < 2 ^ 16 ∧ row[2].val < 2 ^ 16 ∧
      row[3].val < 2 ^ 8) ∧
  (rawImage.map Prod.fst).Nodup ∧
  (∃ row, pcStartRowsOf data = [row] ∧ RowValuesBelow (2 ^ 16) row) ∧
  ∃ row, initClockRowsOf data = [row]

/-- Canonical prover data encodes exactly the public program. -/
def StatementFor (data : ProverData (ZMod p)) (program : GuestProgram) : Prop :=
  CanonicalEncoding data ∧ progOf data = program

end SP1Clean.Commit
