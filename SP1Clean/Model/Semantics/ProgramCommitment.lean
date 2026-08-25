import SP1Clean.Model.Machine.Boot
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

/-- A ROM already satisfying the four `GuestProgram` invariants is a fixed point of sanitization. -/
theorem sanitizeRom_eq_self (l : List (BitVec 64 × BitVec 32))
    (nodup : (l.map Prod.fst).Nodup)
    (aligned : ∀ a ∈ l.map Prod.fst, a.toNat % 4 = 0)
    (inWindow : ∀ aw ∈ l, 2 ^ 16 ≤ aw.1.toNat ∧ aw.1.toNat + 4 ≤ 2 ^ 48)
    (fullWidth : ∀ aw ∈ l, aw.2.extractLsb' 0 2 = 0b11#2) :
    sanitizeRom l = l := by
  induction l with
  | nil => rfl
  | cons entry rest ih =>
    have alignedHead : entry.1.toNat % 4 = 0 := aligned entry.1 (by simp)
    have windowHead : 2 ^ 16 ≤ entry.1.toNat ∧ entry.1.toNat + 4 ≤ 2 ^ 48 :=
      inWindow entry (by simp)
    have widthHead : entry.2.extractLsb' 0 2 = 0b11#2 := fullWidth entry (by simp)
    have nodupCons : entry.1 ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using nodup
    have sanitizedRest : sanitizeRom rest = rest :=
      ih nodupCons.2
        (fun a ha => aligned a (by simp only [List.map_cons, List.mem_cons]; exact Or.inr ha))
        (fun aw haw => inWindow aw (List.mem_cons_of_mem entry haw))
        (fun aw haw => fullWidth aw (List.mem_cons_of_mem entry haw))
    rw [sanitizeRom, if_pos ⟨alignedHead, windowHead.1, windowHead.2, widthHead⟩, sanitizedRest]
    congr 1
    apply List.filter_eq_self.mpr
    intro entry' entryMem
    simp only [decide_eq_true_eq]
    intro addressesEq
    exact nodupCons.1 (List.mem_map.mpr ⟨entry', entryMem, addressesEq⟩)

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
sanitization, all byte/16-bit limbs and both 24-bit clock limbs are in range rather than silently
reduced, singleton keys really are singletons, and image addresses are unique. -/
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
  ∃ row, initClockRowsOf data = [row] ∧ RowValuesBelow (2 ^ 24) row

/-- Canonical prover data encodes exactly the public program. -/
def StatementFor (data : ProverData (ZMod p)) (program : GuestProgram) : Prop :=
  CanonicalEncoding data ∧ progOf data = program

/-! ## Canonical honest-prover encoding -/

/-- The one representation-side condition not already supplied by `GuestProgram` and
`GuestProgram.WellFormed`: every initial-memory address fits the committed three-u16-limb address
format.  Image-address uniqueness remains the existing `WellFormed.imageAddressesUnique` fact. -/
def Encodable (program : GuestProgram) : Prop :=
  ∀ entry ∈ program.memImage, entry.1.toNat < 2 ^ 48

/-- Canonical committed image rows always decode to addresses in the representable 48-bit
window.  This is the inverse-direction fact used by soundness: unlike the honest encoder, it does
not need an `Encodable` premise because canonical limb bounds already supply it. -/
theorem CanonicalEncoding.encodable_progOf (data : ProverData (ZMod p))
    (canonical : CanonicalEncoding data) : Encodable (progOf data) := by
  intro entry entryMem
  rw [progOf] at entryMem
  obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp entryMem
  have bounds := canonical.2.2.1 row rowMem
  simp only [imageEntryOf, BitVec.toNat_ofNat]
  omega

/-- A canonical statement binding transfers the representation's 48-bit image-address bound to
the named semantic program. -/
theorem StatementFor.encodable {data : ProverData (ZMod p)} {program : GuestProgram}
    (statement : StatementFor data program) : Encodable program := by
  rw [← statement.2]
  exact statement.1.encodable_progOf data

/-- The initial shard clock fits the committed pair of 24-bit limbs. -/
def InitialClockEncodable (initialClock : ℕ) : Prop :=
  initialClock < 2 ^ 48

/-- Encode one semantic ROM entry as `[pc0, pc1, pc2, w_lo, w_hi]`. -/
def romRowOf (entry : BitVec 64 × BitVec 32) : Vector (ZMod p) 5 :=
  #v[((entry.1.toNat % 2 ^ 16 : ℕ) : ZMod p),
     ((entry.1.toNat / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
     ((entry.1.toNat / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p),
     ((entry.2.toNat % 2 ^ 16 : ℕ) : ZMod p),
     ((entry.2.toNat / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p)]

/-- Encode one initial-memory byte as `[a0, a1, a2, byte]`. -/
def imageRowOf (entry : BitVec 64 × BitVec 8) : Vector (ZMod p) 4 :=
  #v[((entry.1.toNat % 2 ^ 16 : ℕ) : ZMod p),
     ((entry.1.toNat / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
     ((entry.1.toNat / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p),
     (entry.2.toNat : ZMod p)]

/-- Encode the entry point in the committed three-u16-limb format. -/
def pcStartRowOf (pc : BitVec 64) : Vector (ZMod p) 3 :=
  #v[((pc.toNat % 2 ^ 16 : ℕ) : ZMod p),
     ((pc.toNat / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
     ((pc.toNat / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p)]

/-- Encode a 48-bit shard clock as `[clk_high, clk_low]`, with two canonical 24-bit limbs. -/
def initClockRowOf (initialClock : ℕ) : Vector (ZMod p) 2 :=
  #v[((initialClock / 2 ^ 24 : ℕ) : ZMod p),
     ((initialClock % 2 ^ 24 : ℕ) : ZMod p)]

/-- Canonical committed data for an honest program at an arbitrary shard clock.  The encoder is
total and proof-independent; every non-reserved key/arity is empty.  `Encodable`,
`InitialClockEncodable`, and `GuestProgram.WellFormed` are needed only when proving canonicality
and inverse laws. -/
def dataOfAt (program : GuestProgram) (initialClock : ℕ) : ProverData (ZMod p) :=
  fun key arity =>
    match key, arity with
    | "sp1.rom", 5 => (program.rom.map (romRowOf (p := p))).toArray
    | "sp1.image", 4 => (program.memImage.map (imageRowOf (p := p))).toArray
    | "sp1.pc_start", 3 => #[pcStartRowOf (p := p) program.pc_start]
    | "sp1.init_clk", 2 => #[initClockRowOf (p := p) initialClock]
    | _, _ => #[]

/-- Canonical committed data at the genesis clock `1`. -/
def dataOf (program : GuestProgram) : ProverData (ZMod p) :=
  dataOfAt program 1

@[simp] theorem romRowsOf_dataOfAt (program : GuestProgram) (initialClock : ℕ) :
    romRowsOf (dataOfAt (p := p) program initialClock) =
      program.rom.map (romRowOf (p := p)) := by
  simp [romRowsOf, dataOfAt]

@[simp] theorem imageRowsOf_dataOfAt (program : GuestProgram) (initialClock : ℕ) :
    imageRowsOf (dataOfAt (p := p) program initialClock) =
      program.memImage.map (imageRowOf (p := p)) := by
  simp [imageRowsOf, dataOfAt]

@[simp] theorem pcStartRowsOf_dataOfAt (program : GuestProgram) (initialClock : ℕ) :
    pcStartRowsOf (dataOfAt (p := p) program initialClock) =
      [pcStartRowOf (p := p) program.pc_start] := by
  simp [pcStartRowsOf, dataOfAt]

@[simp] theorem initClockRowsOf_dataOfAt (program : GuestProgram) (initialClock : ℕ) :
    initClockRowsOf (dataOfAt (p := p) program initialClock) =
      [initClockRowOf (p := p) initialClock] := by
  simp [initClockRowsOf, dataOfAt]

@[simp] theorem romRowsOf_dataOf (program : GuestProgram) :
    romRowsOf (dataOf (p := p) program) = program.rom.map (romRowOf (p := p)) := by
  simp [dataOf]

@[simp] theorem imageRowsOf_dataOf (program : GuestProgram) :
    imageRowsOf (dataOf (p := p) program) = program.memImage.map (imageRowOf (p := p)) := by
  simp [dataOf]

@[simp] theorem pcStartRowsOf_dataOf (program : GuestProgram) :
    pcStartRowsOf (dataOf (p := p) program) = [pcStartRowOf (p := p) program.pc_start] := by
  simp [dataOf]

@[simp] theorem initClockRowsOf_dataOf (program : GuestProgram) :
    initClockRowsOf (dataOf (p := p) program) = [#v[0, 1]] := by
  simp [dataOf, initClockRowOf]

private theorem val_natCast_eq_of_lt_2_16 [Fact p.Prime] [Fact (2 ^ 17 < p)]
    {n : ℕ} (nLt : n < 2 ^ 16) : ((n : ZMod p)).val = n := by
  have hp : 2 ^ 17 < p := Fact.out
  exact ZMod.val_natCast_of_lt (by omega)

/-- Every cell of an encoded ROM row is a canonical u16 limb. -/
theorem romRowOf_valuesBelow [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (entry : BitVec 64 × BitVec 32) : RowValuesBelow (p := p) (2 ^ 16) (romRowOf entry) := by
  intro value valueMem
  simp only [romRowOf, Vector.toList_mk, List.mem_cons, List.not_mem_nil, or_false] at valueMem
  rcases valueMem with rfl | rfl | rfl | rfl | rfl
  all_goals rw [val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num))]
  all_goals exact Nat.mod_lt _ (by norm_num)

/-- The four cells of an encoded image row have their canonical address-limb/byte bounds. -/
theorem imageRowOf_valuesBelow [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (entry : BitVec 64 × BitVec 8) :
    (imageRowOf (p := p) entry)[0].val < 2 ^ 16 ∧
    (imageRowOf (p := p) entry)[1].val < 2 ^ 16 ∧
    (imageRowOf (p := p) entry)[2].val < 2 ^ 16 ∧
    (imageRowOf (p := p) entry)[3].val < 2 ^ 8 := by
  simp only [imageRowOf, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num))]
    exact Nat.mod_lt _ (by norm_num)
  · rw [val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num))]
    exact Nat.mod_lt _ (by norm_num)
  · rw [val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num))]
    exact Nat.mod_lt _ (by norm_num)
  · rw [val_natCast_eq_of_lt_2_16 (by have := entry.2.isLt; omega)]
    exact entry.2.isLt

/-- The encoded entry-point row has three canonical u16 limbs. -/
theorem pcStartRowOf_valuesBelow [Fact p.Prime] [Fact (2 ^ 17 < p)] (pc : BitVec 64) :
    RowValuesBelow (p := p) (2 ^ 16) (pcStartRowOf pc) := by
  intro value valueMem
  simp only [pcStartRowOf, Vector.toList_mk, List.mem_cons, List.not_mem_nil, or_false] at valueMem
  rcases valueMem with rfl | rfl | rfl
  all_goals rw [val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num))]
  all_goals exact Nat.mod_lt _ (by norm_num)

/-- An in-range encoded shard clock consists of two canonical 24-bit field limbs. -/
theorem initClockRowOf_valuesBelow
    (initialClock : ℕ) (encodable : InitialClockEncodable initialClock) :
    RowValuesBelow (p := p) (2 ^ 24) (initClockRowOf initialClock) := by
  have clockLt : initialClock < 2 ^ 48 := encodable
  intro value valueMem
  simp only [initClockRowOf, Vector.toList_mk, List.mem_cons, List.not_mem_nil, or_false]
    at valueMem
  rcases valueMem with rfl | rfl
  · rw [ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  · rw [ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by norm_num))

private theorem reassembleAddress [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (address : BitVec 64) (addressLt : address.toNat < 2 ^ 48) :
    BitVec.ofNat 64
      (((address.toNat % 2 ^ 16 : ℕ) : ZMod p).val +
        ((address.toNat / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p).val * 2 ^ 16 +
        ((address.toNat / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p).val * 2 ^ 32) = address := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,
    val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num)),
    val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num)),
    val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num))]
  omega

/-- Encoding then decoding one in-range ROM row recovers the semantic entry. -/
theorem romEntryOf_romRowOf [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (entry : BitVec 64 × BitVec 32) (addressLt : entry.1.toNat < 2 ^ 48) :
    romEntryOf (romRowOf (p := p) entry) = entry := by
  apply Prod.ext
  · simpa only [romEntryOf, romRowOf, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] using
      reassembleAddress (p := p) entry.1 addressLt
  · apply BitVec.eq_of_toNat_eq
    simp only [romEntryOf, romRowOf, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
    rw [val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num)),
      val_natCast_eq_of_lt_2_16 (Nat.mod_lt _ (by norm_num))]
    have wordLt := entry.2.isLt
    omega

/-- Encoding then decoding one in-range image row recovers the semantic byte entry. -/
theorem imageEntryOf_imageRowOf [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (entry : BitVec 64 × BitVec 8) (addressLt : entry.1.toNat < 2 ^ 48) :
    imageEntryOf (imageRowOf (p := p) entry) = entry := by
  apply Prod.ext
  · simpa only [imageEntryOf, imageRowOf, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] using
      reassembleAddress (p := p) entry.1 addressLt
  · apply BitVec.eq_of_toNat_eq
    simp only [imageEntryOf, imageRowOf, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
    rw [val_natCast_eq_of_lt_2_16 (by have := entry.2.isLt; omega)]
    simp [Nat.mod_eq_of_lt entry.2.isLt]

private theorem pcStart_lt_of_wellFormed (program : GuestProgram)
    (wellFormed : program.WellFormed) : program.pc_start.toNat < 2 ^ 48 := by
  obtain ⟨_, fetch⟩ := wellFormed.entryPointPresent
  rw [GuestProgram.fetchWord, Option.map_eq_some_iff] at fetch
  obtain ⟨entry, entryFind, -⟩ := fetch
  have entryMem := List.mem_of_find?_eq_some entryFind
  have addressEq : entry.1 = program.pc_start := by
    have := List.find?_some entryFind
    simpa using this
  have inWindow := program.rom_in_window entry entryMem
  rw [addressEq] at inWindow
  omega

private theorem decodedRomRows_dataOfAt [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (initialClock : ℕ) :
    (romRowsOf (dataOfAt (p := p) program initialClock)).map romEntryOf = program.rom := by
  rw [romRowsOf_dataOfAt, List.map_map]
  calc
    program.rom.map (romEntryOf ∘ romRowOf (p := p)) = program.rom.map id :=
      List.map_congr_left fun entry entryMem => by
        simp only [Function.comp_apply, id_eq]
        exact romEntryOf_romRowOf entry (by
          have := program.rom_in_window entry entryMem
          omega)
    _ = program.rom := List.map_id program.rom

private theorem decodedImageRows_dataOfAt [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (initialClock : ℕ) (encodable : Encodable program) :
    (imageRowsOf (dataOfAt (p := p) program initialClock)).map imageEntryOf =
      program.memImage := by
  rw [imageRowsOf_dataOfAt, List.map_map]
  calc
    program.memImage.map (imageEntryOf ∘ imageRowOf (p := p)) = program.memImage.map id :=
      List.map_congr_left fun entry entryMem => by
        simp only [Function.comp_apply, id_eq]
        exact imageEntryOf_imageRowOf entry (encodable entry entryMem)
    _ = program.memImage := List.map_id program.memImage

/-- The arbitrary-shard encoder emits a canonical commitment whenever the semantic program is
loader-well-formed and both representation-side range conditions hold.  This theorem establishes
canonicality of the emitted field row; exact recovery of the source clock additionally requires
`2 ^ 24 < p`, as stated by `initClkNat_dataOfAt`. -/
theorem dataOfAt_canonicalEncoding [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (initialClock : ℕ) (wellFormed : program.WellFormed)
    (encodable : Encodable program) (clockEncodable : InitialClockEncodable initialClock) :
    CanonicalEncoding (dataOfAt (p := p) program initialClock) := by
  have rawRomEq := decodedRomRows_dataOfAt (p := p) program initialClock
  have rawImageEq := decodedImageRows_dataOfAt (p := p) program initialClock encodable
  simp only [CanonicalEncoding]
  rw [rawRomEq, rawImageEq]
  refine ⟨sanitizeRom_eq_self program.rom program.rom_nodup program.rom_aligned
      program.rom_in_window program.rom_full_width, ?_, ?_, wellFormed.imageAddressesUnique,
    ⟨pcStartRowOf (p := p) program.pc_start, pcStartRowsOf_dataOfAt program initialClock,
      pcStartRowOf_valuesBelow program.pc_start⟩,
    ⟨initClockRowOf (p := p) initialClock, initClockRowsOf_dataOfAt program initialClock,
      initClockRowOf_valuesBelow initialClock clockEncodable⟩⟩
  · intro row rowMem
    rw [romRowsOf_dataOfAt] at rowMem
    obtain ⟨entry, -, rfl⟩ := List.mem_map.mp rowMem
    exact romRowOf_valuesBelow entry
  · intro row rowMem
    rw [imageRowsOf_dataOfAt] at rowMem
    obtain ⟨entry, -, rfl⟩ := List.mem_map.mp rowMem
    exact imageRowOf_valuesBelow entry

/-- The total genesis encoder emits a canonical commitment whenever the semantic program is
loader-well-formed and its byte-image addresses fit the commitment format. -/
theorem dataOf_canonicalEncoding [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (wellFormed : program.WellFormed)
    (encodable : Encodable program) : CanonicalEncoding (dataOf (p := p) program) := by
  simpa only [dataOf] using dataOfAt_canonicalEncoding (p := p) program 1 wellFormed encodable (by
    simp [InitialClockEncodable])

/-- The canonical entry-point key is independent of the shard clock and decodes back to a
well-formed program's entry point. -/
theorem pcStartOf_dataOfAt [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (initialClock : ℕ) (wellFormed : program.WellFormed) :
    pcStartOf (dataOfAt (p := p) program initialClock) = program.pc_start := by
  have addressLt := pcStart_lt_of_wellFormed program wellFormed
  simp only [pcStartOf, dataOfAt, pcStartRowOf, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, List.toList_toArray]
  exact reassembleAddress (p := p) program.pc_start addressLt

/-- The genesis specialization preserves the existing entry-point round trip. -/
theorem pcStartOf_dataOf [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (wellFormed : program.WellFormed) :
    pcStartOf (dataOf (p := p) program) = program.pc_start := by
  simpa only [dataOf] using pcStartOf_dataOfAt (p := p) program 1 wellFormed

private theorem guestProgram_eq_of_data_eq {left right : GuestProgram}
    (romEq : left.rom = right.rom) (pcEq : left.pc_start = right.pc_start)
    (imageEq : left.memImage = right.memImage) : left = right := by
  cases left
  cases right
  simpa only [GuestProgram.mk.injEq] using ⟨romEq, pcEq, imageEq⟩

/-- Decoding canonical arbitrary-shard prover data recovers the original semantic program. -/
theorem progOf_dataOfAt [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (initialClock : ℕ) (wellFormed : program.WellFormed)
    (encodable : Encodable program) :
    progOf (dataOfAt (p := p) program initialClock) = program := by
  apply guestProgram_eq_of_data_eq
  · simp only [progOf]
    rw [decodedRomRows_dataOfAt, sanitizeRom_eq_self program.rom program.rom_nodup
      program.rom_aligned program.rom_in_window program.rom_full_width]
  · exact pcStartOf_dataOfAt program initialClock wellFormed
  · simpa only [progOf] using
      decodedImageRows_dataOfAt (p := p) program initialClock encodable

/-- Decoding the genesis specialization preserves the existing program round trip. -/
theorem progOf_dataOf [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (wellFormed : program.WellFormed)
    (encodable : Encodable program) : progOf (dataOf (p := p) program) = program := by
  simpa only [dataOf] using progOf_dataOfAt (p := p) program 1 wellFormed encodable

/-- Canonical arbitrary-shard prover data satisfies the public statement binding for its source
program. -/
theorem dataOfAt_statementFor [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (initialClock : ℕ) (wellFormed : program.WellFormed)
    (encodable : Encodable program) (clockEncodable : InitialClockEncodable initialClock) :
    StatementFor (dataOfAt (p := p) program initialClock) program :=
  ⟨dataOfAt_canonicalEncoding program initialClock wellFormed encodable clockEncodable,
    progOf_dataOfAt program initialClock wellFormed encodable⟩

/-- Canonical honest-prover data satisfies the public statement binding for its source program. -/
theorem dataOf_statementFor [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) (wellFormed : program.WellFormed)
    (encodable : Encodable program) : StatementFor (dataOf (p := p) program) program :=
  ⟨dataOf_canonicalEncoding program wellFormed encodable,
    progOf_dataOf program wellFormed encodable⟩

/-- The committed clock of an in-range arbitrary-shard encoding decodes exactly.  The stronger field
bound is necessary here because both field representatives are genuine 24-bit limbs. -/
@[simp] theorem initClkNat_dataOfAt [Fact p.Prime] [Fact (2 ^ 24 < p)]
    (program : GuestProgram) (initialClock : ℕ)
    (encodable : InitialClockEncodable initialClock) :
    initClkNat (dataOfAt (p := p) program initialClock) = initialClock := by
  have hp : 2 ^ 24 < p := Fact.out
  have clockLt : initialClock < 2 ^ 48 := encodable
  have highLt : initialClock / 2 ^ 24 < p := by omega
  have lowLt : initialClock % 2 ^ 24 < p :=
    lt_trans (Nat.mod_lt _ (by norm_num)) hp
  simp only [initClkNat, dataOfAt, initClockRowOf, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, List.toList_toArray]
  rw [ZMod.val_natCast_of_lt highLt, ZMod.val_natCast_of_lt lowLt]
  omega

@[simp] theorem initClkNat_dataOf [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (program : GuestProgram) :
    initClkNat (dataOf (p := p) program) = 1 := by
  have hp : 2 ^ 17 < p := Fact.out
  simp [initClkNat, dataOf, dataOfAt, initClockRowOf]
  rw [← Nat.cast_one (R := ZMod p), ZMod.val_natCast_of_lt (by omega)]

end SP1Clean.Commit
